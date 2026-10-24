//! The arity-shaped formers in the lowering: the telescope `#{…}`, the sum
//! over labels `+{…}` and the lazy record over labels `&{…}`, at the type,
//! the value and the observation, and the telescope Π `(x : A, …) => C`. The
//! patterns of the first two are read by the match compiler (`native`).
//!
//! # One core former per reading of a delimiter
//!
//! A positional telescope is the core's product of its entries, of any
//! arity: `#{}` is the unit, `#{A}` the product of one component, distinct
//! from `A`, and its value `#{a}` the tuple of one. A labelled telescope is
//! the core's record, whose fields the labels key, so two records that list
//! the same fields in another order are one record. A sum over labels is the
//! core's sum of its entries in written order, the labels erased; a lazy
//! record over labels is the core's lazy product of its entries in order, of
//! any arity: `&{}` is the terminal computation type, `&{C}` the lazy product
//! of one, and `&{C, D, E}` the same former as the chain `C & D & E`.
//!
//! An entry is positional, labelled by its index, or labelled by name, and a
//! form holds one kind throughout. An index is a position: the indices of a
//! form are exactly `0` to `n - 1`, each once, and the entries are reordered
//! by them, so `#{ .1 = b, .0 = a }` is `#{a, b}`. A label names one entry.
//!
//! - Alternatives: a record as the product of its fields in written order,
//!   which makes field order observable and two spellings of one record two
//!   types; mixed positional and labelled entries, which leaves an unlabelled
//!   entry's label to a rule the reader has to know; a lazy record as the
//!   record of its entries' thunks, `U &{l : C} ≅ #{l : U C}`, which loses the
//!   lazy product's η and makes the codata it abstracts matchable data.
//! - Reversal: a core sum or lazy record keyed by labels would carry them where
//!   the positional formers drop them.
//!
//! The kernel carries the lazy product as its own node, so a declaration
//! holding one checks and crosses the kernel boundary like any other
//! ([#203](https://github.com/gandr-lang/gandr/issues/203)).
//!
//! # A label's index is read from the type the source states
//!
//! The core's sum and lazy record are positional, so a labelled injection
//! `+{ .ok = a }`, a labelled sum pattern, a labelled copattern block and an
//! observation `m.get` each need the position their label names, which only
//! a type over the same labels says. The lowering reads it from the type the
//! source states at the form, through parentheses: an annotation `(e : T)`
//! for an injection, the scrutinee's written type for a pattern (a parameter
//! or a declaration with a signature), the answer its position states for a
//! copattern block (a function's result or a match's answer), and the written
//! type `+U &{…}` of the name an observation selects from. Without one the
//! form is refused as unannotated; a positional label `.1` names its index
//! itself and needs no type, except where a sum pattern must know how many
//! summands to cover. A type named by a declaration is not unfolded. A
//! record's field needs no index either: the core's record is keyed by its
//! labels, so a selection `e.l` off a value no written type states projects
//! `l` itself, and the checker reads the field's type off the record type `e`
//! synthesises.
//!
//! - Alternatives: a checker that elaborates a labelled form against the type
//!   it checks at, which the lowering does not duplicate; reading the
//!   declaration a type name stands for, which makes the lowering evaluate
//!   types.
//! - Reversal: a checker that carries labels and checks a labelled form against
//!   its expected type makes the stated type optional.
//!
//! # A later label reads an earlier one: the dependent record
//!
//! A labelled telescope type binds each label in the entries after it, as a
//! telescope Π binds its entries: `#{n : Integer, v : Path(Integer, n, n)}`.
//! Where no later entry names an earlier label it is the record of its
//! fields, so a record's type is unchanged by the labels it binds; where one
//! does, it is the core's dependent pairs nested to the right, the labels
//! erased, each link a `Σ` when a later entry names its label and the eager
//! product of two otherwise: `#{a : A, b : B, c : C(a)}` is `Σ a : A. B ×
//! C(a)`. Its value is the tuple of its entries in written order, nested
//! as the type is, `#{x, y}` for two.
//!
//! Whether a later entry names a label is read from the source: a name
//! spelling the label anywhere in a later entry marks the label's frame
//! mentioned before any entry is read. A pattern at the type is compiled
//! where its match is classified, which may come before the names in the
//! entries resolve, so the frames' mention, the type's links and the
//! pattern's splits are all this one syntactic reading. A name spelling the
//! label under a binder of its own in a later entry links the label by a `Σ`
//! whose second factor does not read it, which is that factor's product.
//!
//! The labels name places: a selection `p.v` off a name whose written type is
//! a type over labels projects the entry the label names along the nesting,
//! `p.1` in the core, whose type reads the first component as `p.0` (the
//! checker's projection rule); a pattern at a scrutinee written with a
//! dependent record, positional `#{m, w}` or labelled `#{.n = m, .v = w}`, is
//! the dependent split of each link, whose motive is the match's answer with
//! the scrutinee abstracted (`lower::native`). A record has no projection,
//! so a selection off one is the projection of a type that is not a
//! dependent pair, which the checker refuses by name.
//!
//! - Alternatives: a labelled dependent record former in the core, which keeps
//!   the labels the lowering erases at the cost of a second eliminator beside
//!   the split; a record whose later entries cannot name an earlier label,
//!   which leaves the dependent record unwritable.
//! - Reversal: a core former keyed by labels would carry them where the nested
//!   pairs drop them.
//!
//! # A session entry reads the select and the offer
//!
//! The sum and the lazy record over labels whose entries are session forms
//! are the session select and offer, one former read in the zone its type is
//! written in: braces at a type's root whose every entry is a session form —
//! `!A. S`, `?A. S`, `end`, `mu t. S`, or braces of session forms — are read
//! whole as a session type (the `lower::session` module), and braces mixing
//! session forms with other types are refused as a misplaced entry. Inside a
//! protocol the braces are the select and the offer whatever their entries,
//! so a branch continuing at a recursion variable reads there.
//!
//! # A telescope Π binds an entry a later type names
//!
//! `(x : A, y : B(x)) => C` is `+U (Π x : A. Π y : B(x). -F C)`: an entry is a
//! dependent arrow exactly where a later entry or the codomain names its
//! binder, as a type or as a value standing in one, and a plain arrow
//! everywhere else, an unnamed entry always. A variable written in a later
//! entry counts only the dependent arrows before it. The dependent arrow
//! `(x : A) -> C` reads by the same rule: a Π where `C` names `x`, the plain
//! arrow otherwise. So `(n : Integer) => Integer` is the type `def f(n :
//! Integer) -> -F Integer` declares, `(n : Integer) -> -F Integer` the
//! computation under its thunk, and a model's operation whose clause binds an
//! index nothing later reads converts with the member that implements it.
//!
//! - Recorded choice, reversed: the dependent arrow's introduction (#266) read
//!   every named binder of `(x : A) -> C` as a Π whether or not `C` names it,
//!   the author's spelling taken as written so a transport motive's two entries
//!   always bind.
//! - Change: the arrow and the telescope entry bind exactly where a later type
//!   names their binder, as a function's parameters do.
//! - Reason: the kernel kept a Π whose codomain ignores its binder and the
//!   plain arrow over the same children distinct, and asked the producer to
//!   emit the dependent former only where the codomain is scoped; reading the
//!   spelling as written made `def g : (n : Integer) => Integer` and the `def
//!   g(n : Integer) -> -F Integer` that defines it two types, and a model's
//!   `def` members unable to meet the components `Model(S)` derives. A
//!   transport motive is unaffected: the motive reader takes a plain arrow and
//!   a Π alike (`lower::identity`).
//! - Alternatives: a Π for every entry once any entry is named, which reads as
//!   one rule but leaves the same two types.
//! - Reversal, fired (#577): conversion now identifies a Π whose codomain
//!   ignores its binder with the plain arrow, in the checker and the kernel,
//!   because a family applied at its binder (`always(x)`) is a Π no producer
//!   can narrow before the family is read. The choice is unobservable to
//!   conversion, and the lowering keeps it for the reading it gives the
//!   printer.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Frame;
use super::LabelRead;
use super::Lowered;
use super::Lowerer;
use super::Parameter;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::Stretch;
use super::closed;
use super::exhausted;
use super::lowered;
use super::native::Answer;
use super::native::answered;
use super::stretch;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::origin::Origin;
use crate::resolve::Mentioned;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::binder_site;
use crate::resolve::binder_type;
use crate::unbuilt::Unbuilt;

#[cfg(test)]
mod tests;

/// A copattern clause read as a body of its own: no statements, the clause
/// its last computation.
///
/// # Specification
/// trivial.
pub(super) const fn clause_body(clause: NodeIndex) -> Block
{
    Block {
        statements: Stretch { start: 0, end: 0 },
        last: clause,
    }
}

/// How an entry of an arity-shaped form is labelled.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: an index and a label each carry where they are written.
/// - executable: none — the key holds no form to check its tile against.
///
/// # Adequacy
/// - hypothesis: L3 — positional, indexed and labelled entries each lower to
///   their own former, and mixing them is refused.
/// - witness: `lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Key<'source>
{
    /// Unlabelled: the entry's place in written order labels it.
    Positional,
    /// `.i`: labelled by its index, spelled and written at the tile.
    Index(usize, SurfaceName<'source>, Placed),
    /// `l` or `.l`: labelled by name, written at the tile or the key form.
    Label(SurfaceName<'source>, Placed),
}

/// What an entry of an arity-shaped form holds.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: an operand is a hole's form; a pun is the label tile it binds.
/// - executable: none — the record holds no form to check against.
///
/// # Adequacy
/// - hypothesis: L3 — a punned pattern entry binds its label, a renamed one its
///   pattern.
/// - witness: `lower::native::tests::telescope_patterns_split_and_project`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Held
{
    /// The entry's operand.
    Operand(Placed),
    /// A pattern entry `.l` with no pattern: it binds its own label.
    Punned(Placed),
}

impl Held
{
    /// Where the entry's content is written.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn at(self) -> Placed
    {
        match self {
            Self::Operand(at) | Self::Punned(at) => at,
        }
    }
}

/// One entry of an arity-shaped form, as written.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the key and what the entry holds.
/// - executable: none — the record holds no form to check against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Key`].
/// - witness: `lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Entry<'source>
{
    /// How the entry is labelled.
    pub key: Key<'source>,
    /// What the entry holds.
    pub held: Held,
}

impl Entry<'_>
{
    /// Where the entry's label is written, or its content when it has none.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn keyed_at(self) -> Placed
    {
        match self.key {
            Key::Positional => self.held.at(),
            Key::Index(_, _, at) | Key::Label(_, at) => at,
        }
    }
}

/// The entries of an arity-shaped form, of one kind throughout.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: positional entries in index order; labelled entries in written
///   order, each label once.
/// - executable: none — [`arrange`] establishes the order.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Key`].
/// - witness: `lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Arranged<'source>
{
    /// Entries labelled by place or by index, in index order.
    Positional(Vec<Entry<'source>>),
    /// Entries labelled by name, in written order.
    Labelled(Vec<Entry<'source>>),
}

/// What the hole-led entries of a telescope value read as.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a telescope's entries in written order; an update's base and the
///   fields it writes, in written order.
/// - executable: none — [`Lowerer::hole_entries`] reads it.
///
/// # Adequacy
/// - hypothesis: L3 — a record and an update over the same labels lower to
///   different formers.
/// - witness: `lower::arity::tests::a_record_update_lowers_to_its_base_and_its_fields`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Telescoped<'source>
{
    /// The telescope's own entries.
    Entries(Vec<Entry<'source>>),
    /// The update `#{ e | l = a, … }`: its base, and the fields it writes.
    Update(Placed, Vec<Entry<'source>>),
}

/// The zone a type form is read in: a protocol's, or every other type's.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one variant per zone.
/// - executable: none — a fieldless tag.
///
/// # Adequacy
/// - hypothesis: L3 — the same braces over value types, over session types,
///   over braces of session types, and mixed.
/// - witness: `lower::arity::tests::a_session_entry_reads_the_select_and_the_offer`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum TypeZone
{
    /// A session form: a protocol's state.
    Session,
    /// Any other type form.
    Ordinary,
}

/// What the operand of an observation is observed at: a type written for it,
/// or the codata family the observation it is returns.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one variant per way the operand's type is known.
/// - executable: none — the classification reads the type it names.
///
/// # Adequacy
/// - hypothesis: L3 — a name's thunk, a call's result, and a link of a chain of
///   observations.
/// - witness: `lower::arity::tests::an_observation_projects_its_entry`
/// - witness: `lower::arity::tests::a_chain_of_observations_projects_each_link_1106`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Subject
{
    /// The type at the node: a thunk the operand holds when thunked, the
    /// computation the operand runs otherwise, its names resolved under the
    /// frame.
    Written(NodeIndex, Thunked, Frame),
    /// The family declared at the constant, the computation the operand runs.
    Family(ConstantIndex),
}

/// The entry an observation selects of a lazy record, or a selection of a
/// dependent record: its index among `count` entries.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `index < count` where the classification built it.
/// - executable: none — the classification checks the label it read.
///
/// # Adequacy
/// - hypothesis: L3 — the first, a middle and the last entry of a lazy record
///   of three each project their own component.
/// - witness: `lower::arity::tests::an_observation_projects_its_entry`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Observed
{
    /// The selected entry's index.
    pub index: usize,
    /// How many entries the lazy record has.
    pub count: usize,
}

/// Whether a lookup reads through a thunk type `+U X` to the `X` it holds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Thunked(pub bool);

/// Whether a link of a type over labels binds: a later entry names the
/// link's label, so the link is a `Σ` and a split of it reads the match's
/// motive at its scrutinee.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Dependent(pub bool);

/// Whether a form was read as an arity-shaped former and planned.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Planned(pub bool);

/// The place of an entry among the entries a type states, counting from
/// zero.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Place(pub usize);

quenchant_shape::reason_enum! {
    /// Why no type over labels is stated where a form needs one.
    pub mod stated_labels {
        /// The type the source states is not the former the form needs.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The stated type, through parentheses, is another former.
            Otherwise,
            /// The stated type over labels is a record: no later entry names
            /// an earlier label.
            Independent,
        }
    }
}

/// Order `entries` by their keys, refusing a form that mixes kinds.
///
/// # Specification
/// - requires: `entries` are the entries of the form at `site`.
/// - ensures: positional entries in written order; indexed entries reordered by
///   index when the indices are exactly `0` to `n - 1`; labelled entries in
///   written order.
/// - fails: a misplaced tile at the first entry of another kind than the first
///   entry's, and at an index out of range; a duplicate definition at a label
///   or an index written twice.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`] and
/// [`LoweringRefusal::DuplicateDefinition`].
///
/// # Adequacy
/// - hypothesis: L3 — reordered indices, a gap, a repeated index and label, and
///   mixed kinds, each asserted as the exact order or refusal.
/// - witness: `lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[spec(
    captures: count = entries.len(),
    ensures: |ret| ret.as_ref().map_or(true, |arranged| match *arranged {
        | Arranged::Positional(ref ordered) | Arranged::Labelled(ref ordered) => ordered.len() == count,
    }),
)]
pub(super) fn arrange<'source>(
    site: Site,
    entries: Vec<Entry<'source>>,
) -> Result<Arranged<'source>, LoweringRefusal<'source>>
{
    let Some(&first) = entries.first()
    else {
        return Ok(Arranged::Positional(entries));
    };
    match first.key {
        Key::Positional => {
            if let Some(stray) = entries
                .iter()
                .find(|entry| !matches!(entry.key, Key::Positional))
            {
                return Err(site.fault(stray.keyed_at().span, FormFault::MisplacedTile));
            }
            Ok(Arranged::Positional(entries))
        },
        Key::Label(..) => {
            let mut seen: BTreeMap<SurfaceName<'source>, Placed> = BTreeMap::new();
            for entry in &entries {
                let Key::Label(name, written) = entry.key
                else {
                    return Err(site.fault(entry.keyed_at().span, FormFault::MisplacedTile));
                };
                if let Some(&earlier) = seen.get(&name) {
                    return Err(LoweringRefusal::DuplicateDefinition {
                        span: written.span,
                        name,
                        first: earlier.span,
                    });
                }
                let _first = seen.insert(name, written);
            }
            Ok(Arranged::Labelled(entries))
        },
        Key::Index(..) => {
            let mut slots: Vec<Option<Entry<'source>>> = alloc::vec![None; entries.len()];
            for entry in &entries {
                let Key::Index(index, name, written) = entry.key
                else {
                    return Err(site.fault(entry.keyed_at().span, FormFault::MisplacedTile));
                };
                let Some(slot) = slots.get_mut(index)
                else {
                    return Err(site.fault(written.span, FormFault::MisplacedTile));
                };
                if let Some(earlier) = *slot {
                    return Err(LoweringRefusal::DuplicateDefinition {
                        span: written.span,
                        name,
                        first: earlier.keyed_at().span,
                    });
                }
                *slot = Some(*entry);
            }
            Ok(Arranged::Positional(slots.into_iter().flatten().collect()))
        },
    }
}

/// Read the separator after an entry: a comma, or the closer `closer` left
/// for the loop to read.
///
/// # Specification
/// - requires: `cursor` stands just past an entry of the form at `site`.
/// - ensures: a comma is consumed; a closer is left in place.
/// - fails: a misplaced tile at anything else.
/// - panics: none.
///
/// # Errors
/// [`LoweringRefusal::MalformedForm`].
///
/// # Adequacy
/// - hypothesis: L3 — trailing commas and one-entry lists read alike.
/// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
#[spec(ensures: |ret| ret.is_err() || matches!(cursor.peek(), Maybe::Absent(_) | Maybe::Present(_)))]
fn separated<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    closer: TileName,
) -> Result<(), LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
        && let Maybe::Absent(_) = cursor.at(closer)
    {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }

    Ok(())
}

/// The nested-pair path to the entry `observed` selects of a dependent
/// record: the sides to project along, innermost first.
///
/// # Specification
/// - requires: `observed.index < observed.count` and `observed.count >= 2`.
/// - ensures: `index` rights, then a left unless the entry is the last.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Observed`], over the dependent record's nesting.
/// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
#[spec(ensures: |ret| ret.iter().filter(|&&side| side == Side::Right).count() == observed.index)]
fn path(observed: Observed) -> Vec<Side>
{
    let last = observed.index.saturating_add(1) >= observed.count;
    let mut sides = alloc::vec![Side::Right; observed.index];
    if !last {
        sides.push(Side::Left);
    }

    sides
}

impl<'source> Lowerer<'_, 'source>
{
    /// The named kind and former of the form at `at`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the form's kind and former; nothing for a node that is no
    ///   form.
    /// - fails: [`LoweringRefusal::UnknownMold`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type entry's key is told from its type by kind.
    /// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn form_at(
        &self,
        at: Placed,
    ) -> Result<Option<(FormName, Former)>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(at.node)
        else {
            return Ok(None);
        };

        Ok(match shape_of(self.pbg, node)? {
            Shape::Form { name, former } => Some((name, former)),
            Shape::Root | Shape::Repair(_) | Shape::Layout => None,
        })
    }

    /// Read a label after its dot: `.l` or `.i`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the label's `.`.
    /// - ensures: a name for an identifier, an index for a decimal number.
    /// - fails: a misplaced tile for anything else.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — named and indexed labels each reach their former.
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| !matches!(ret, Ok(Key::Positional)))]
    pub(super) fn dotted(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Key<'source>, LoweringRefusal<'source>>
    {
        closed(site, cursor, TileName::DOT)?;
        if let Maybe::Present(word) = cursor.tile(TileName::IDENTIFIER) {
            return Ok(Key::Label(self.name_at(word), word));
        }
        let Maybe::Present(number) = cursor.tile(TileName::NUMBER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let name = self.name_at(number);
        let spelled: &str = name.as_ref();

        spelled
            .parse::<usize>()
            .map(|index| Key::Index(index, name, number))
            .map_err(|_overflow| site.fault(number.span, FormFault::MisplacedTile))
    }

    /// Read the entries of a type list up to `closer`: each a bare type, or
    /// `k : T` whose key is a bare word, lowercase or named as a type is.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the form's opener.
    /// - ensures: every entry in written order, the cursor exhausted.
    /// - fails: a misplaced key or tile, and a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, positional and labelled lists, with and
    ///   without a trailing comma, and a dependent arrow whose binder is named
    ///   as a type is.
    /// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    /// - witness: `lower::arity::tests::a_dependent_arrow_binds_a_type_named_binder_2179`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| matches!(entry.held, Held::Operand(_)))))]
    pub(super) fn type_entries(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
        closer: TileName,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(closer) {
            let first = site.one(cursor.operands())?;
            let entry = if let Maybe::Present(_) = cursor.tile(TileName::COLON) {
                if !matches!(self.form_at(first)?, Some((name, _)) if name == FormName::TYPE_VARIABLE || name == FormName::TYPE_IDENTIFIER)
                {
                    return Err(site.fault(first.span, FormFault::MisplacedTile));
                }
                Entry {
                    key: Key::Label(self.name_at(first), first),
                    held: Held::Operand(site.one(cursor.operands())?),
                }
            }
            else {
                Entry {
                    key: Key::Positional,
                    held: Held::Operand(first),
                }
            };
            entries.push(entry);
            separated(site, cursor, closer)?;
        }
        exhausted(site, cursor)?;

        Ok(entries)
    }

    /// Read the entries `.l <between> e` of a labelled value form up to `}`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the form's opener.
    /// - ensures: every entry in written order, the cursor exhausted.
    /// - fails: a misplaced tile, and a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — labelled telescopes and copattern blocks.
    /// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_answer`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| !matches!(entry.key, Key::Positional))))]
    fn dotted_entries(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
        between: TileName,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let key = self.dotted(site, cursor)?;
            closed(site, cursor, between)?;
            entries.push(Entry {
                key,
                held: Held::Operand(site.one(cursor.operands())?),
            });
            separated(site, cursor, TileName::BRACE_CLOSE)?;
        }
        exhausted(site, cursor)?;

        Ok(entries)
    }

    /// Read the entries `l = e` of a `co` bundle up to `}`, each key a bare
    /// label.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the bundle's `{`.
    /// - ensures: every entry in written order, each labelled by its word, the
    ///   cursor exhausted.
    /// - fails: a misplaced tile, and a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bundle of two fields written out of the stated
    ///   order reads as the lazy record of its labels.
    /// - witness: `lower::arity::tests::a_co_bundle_is_the_lazy_record_of_its_labels`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| matches!(entry.key, Key::Label(..)))))]
    fn bundle_entries(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let Maybe::Present(word) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(site, cursor, TileName::EQUALS)?;
            entries.push(Entry {
                key: Key::Label(self.name_at(word), word),
                held: Held::Operand(site.one(cursor.operands())?),
            });
            separated(site, cursor, TileName::BRACE_CLOSE)?;
        }
        exhausted(site, cursor)?;

        Ok(entries)
    }

    /// Read the hole-led entries of a telescope value up to `}`: each a
    /// positional `e`, or the shorthand `l = e` whose key is a bare name; or
    /// the update `#{ e | l = a, … }`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the telescope's `#{`.
    /// - ensures: every entry in written order, the cursor exhausted; for an
    ///   update, its base and the fields it writes.
    /// - fails: a key that is not a bare name, a misplaced tile — a `|` after
    ///   any entry but one positional first one — and a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit, positional entries, the shorthand, and an
    ///   update.
    /// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
    /// - witness: `lower::arity::tests::a_record_update_lowers_to_its_base_and_its_fields`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |read| match *read {
        | Telescoped::Entries(ref entries) => entries.iter().all(|entry| !matches!(entry.key, Key::Index(..))),
        | Telescoped::Update(_, ref written) => !written.is_empty(),
    }))]
    fn hole_entries(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Telescoped<'source>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let first = site.one(cursor.operands())?;
            let entry = if let Maybe::Present(_) = cursor.tile(TileName::EQUALS) {
                if !matches!(self.form_at(first)?, Some((name, _)) if name == FormName::IDENTIFIER)
                {
                    return Err(site.fault(first.span, FormFault::MisplacedTile));
                }
                Entry {
                    key: Key::Label(self.name_at(first), first),
                    held: Held::Operand(site.one(cursor.operands())?),
                }
            }
            else {
                Entry {
                    key: Key::Positional,
                    held: Held::Operand(first),
                }
            };
            // An update's base is the telescope's one positional entry.
            if let Maybe::Present(bar) = cursor.tile(TileName::BAR) {
                if !entries.is_empty() || entry.key != Key::Positional {
                    return Err(site.fault(bar.span, FormFault::MisplacedTile));
                }
                return Ok(Telescoped::Update(
                    first,
                    self.update_fields(site, cursor, bar)?,
                ));
            }
            entries.push(entry);
            separated(site, cursor, TileName::BRACE_CLOSE)?;
        }
        exhausted(site, cursor)?;

        Ok(Telescoped::Entries(entries))
    }

    /// Read the fields an update writes, `l = e, …`, up to `}`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the update's `|`, at `bar`.
    /// - ensures: one labelled entry per field in written order, the cursor
    ///   exhausted.
    /// - fails: a misplaced tile where a field's name or its `=` should stand,
    ///   and at `bar` when no field is written; a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an update of one field and of two.
    /// - witness: `lower::arity::tests::a_record_update_lowers_to_its_base_and_its_fields`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |written| !written.is_empty() && written.iter().all(|entry| matches!(entry.key, Key::Label(..)))))]
    fn update_fields(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
        bar: Placed,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut written = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let Maybe::Present(word) = cursor.tile(TileName::IDENTIFIER)
            else {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            };
            closed(site, cursor, TileName::EQUALS)?;
            written.push(Entry {
                key: Key::Label(self.name_at(word), word),
                held: Held::Operand(site.one(cursor.operands())?),
            });
            separated(site, cursor, TileName::BRACE_CLOSE)?;
        }
        exhausted(site, cursor)?;
        if written.is_empty() {
            return Err(site.fault(bar.span, FormFault::MisplacedTile));
        }

        Ok(written)
    }

    /// Read the entries of a telescope pattern up to `}`: each a punned
    /// `.l`, a renamed `.l = p`, or a positional `p`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the pattern's `#{`.
    /// - ensures: every entry in written order, the cursor exhausted; a punned
    ///   entry holds its label tile.
    /// - fails: a misplaced tile at an undotted key `k = p`, at a punned index,
    ///   and at a separator out of place; a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — punned, renamed and positional entries, and an
    ///   undotted key.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| !matches!(entry.held, Held::Punned(_)) || matches!(entry.key, Key::Label(..)))))]
    pub(super) fn pattern_entries(
        &self,
        here: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            let entry = if let Maybe::Present(_) = cursor.at(TileName::DOT) {
                let key = self.dotted(here, cursor)?;
                let held = if let Maybe::Present(_) = cursor.tile(TileName::EQUALS) {
                    Held::Operand(here.one(cursor.operands())?)
                }
                else {
                    match key {
                        Key::Label(_, label) => Held::Punned(label),
                        Key::Index(_, _, written) => {
                            return Err(here.fault(written.span, FormFault::MisplacedTile));
                        },
                        Key::Positional => {
                            return Err(here.fault(cursor.here(), FormFault::MisplacedTile));
                        },
                    }
                };
                Entry { key, held }
            }
            else {
                let first = here.one(cursor.operands())?;
                if let Maybe::Present(equals) = cursor.at(TileName::EQUALS) {
                    return Err(here.fault(equals.span, FormFault::MisplacedTile));
                }
                Entry {
                    key: Key::Positional,
                    held: Held::Operand(first),
                }
            };
            entries.push(entry);
            separated(here, cursor, TileName::BRACE_CLOSE)?;
        }
        exhausted(here, cursor)?;

        Ok(entries)
    }

    /// Read the entries of a tuple pattern up to `)`, each positional.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the pattern's `(`.
    /// - ensures: every entry in written order, the cursor exhausted.
    /// - fails: a misplaced tile, and a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`].
    ///
    /// # Termination
    /// Every round consumes at least one piece of the finite cursor or
    /// refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple pattern splits as the telescope does.
    /// - witness: `lower::native::tests::telescope_patterns_split_and_project`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| matches!(entry.key, Key::Positional))))]
    pub(super) fn tuple_entries(
        here: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        while let Maybe::Absent(_) = cursor.tile(TileName::PAREN_CLOSE) {
            entries.push(Entry {
                key: Key::Positional,
                held: Held::Operand(here.one(cursor.operands())?),
            });
            separated(here, cursor, TileName::PAREN_CLOSE)?;
        }
        exhausted(here, cursor)?;

        Ok(entries)
    }

    /// The type the scrutinee `scrutinee` of a match under `frame` was
    /// written with: its binder's or its declaration's, when it is a name, or
    /// the result its function states, when it is a call.
    ///
    /// # Specification
    /// - requires: `scrutinee` is a match's scrutinee.
    /// - ensures: the written type of the binder or the declaration a name
    ///   resolves to; for a `run` binder written with no type, the type its
    ///   computation returns, as [`Self::ran_type`] reads it; for a call, the
    ///   type it returns, as [`Self::called_type`] reads it; nothing for any
    ///   other scrutinee or an untyped name.
    /// - fails: the name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnmarkedSelfReference`],
    /// [`LoweringRefusal::ForwardMemberReference`],
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over a typed parameter reads its sum's arity,
    ///   one over an untyped name refuses a sum pattern, and one over a `run`
    ///   binder or a call splits the record its callee returns.
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    /// - witness: `lower::identity::tests::a_run_binder_splits_the_relation_its_call_returns_656`
    /// - witness: `lower::native::tests::a_call_as_the_scrutinee_splits_the_record_it_returns_1141`
    #[spec(ensures: |ret| ret.is_ok() || !matches!(ret, Err(LoweringRefusal::MalformedForm { .. })))]
    pub(super) fn scrutinee_type(
        &mut self,
        frame: Frame,
        scrutinee: Placed,
    ) -> Result<Maybe<NodeIndex, binder_type::Absent>, LoweringRefusal<'source>>
    {
        if !matches!(self.form_at(scrutinee)?, Some((_, Former::Name))) {
            return self.called_type(frame, scrutinee.node);
        }
        let named = Site {
            at: scrutinee,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };

        Ok(
            match self.resolve_name(named, frame, self.name_at(scrutinee))? {
                Maybe::Present(Resolved::Binder(bound)) => match bound.declared {
                    Maybe::Absent(binder_type::Absent::Untyped) => self.ran_type(bound.binder)?,
                    declared
                    @ (Maybe::Present(_) | Maybe::Absent(binder_type::Absent::Operand)) => declared,
                },
                Maybe::Present(Resolved::Declaration { declared, .. }) => declared,
                Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped),
            },
        )
    }

    /// The type the `run` binder `binder` holds, as the function its
    /// computation calls wrote it: `A` of the function's result `-F A`, as
    /// [`Self::called_type`] reads it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node of `A` when `binder` is a `run` binder written with
    ///   no type whose computation [`Self::called_type`] reads, under the frame
    ///   the computation reads in; the untyped absence otherwise.
    /// - provides: the record layout of a call's result to a match on it, so a
    ///   pattern splits the record a quasi-inverse or an equivalence
    ///   abbreviates as it does at a parameter written with one.
    /// - fails: the callee's resolution refusals;
    ///   [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] reading its forms.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over a `run` binder of a call returning a
    ///   quasi-inverse splits its four components positionally and by label.
    /// - witness: `lower::identity::tests::a_run_binder_splits_the_relation_its_call_returns_656`
    #[spec(ensures: |ret| ret.is_err()
        || matches!(ret, Ok(Maybe::Absent(binder_type::Absent::Untyped)))
        || self.ran.contains_key(&binder))]
    fn ran_type(
        &mut self,
        binder: ScopeId,
    ) -> Result<Maybe<NodeIndex, binder_type::Absent>, LoweringRefusal<'source>>
    {
        let Some(&(frame, bound)) = self.ran.get(&binder)
        else {
            return Ok(Maybe::Absent(binder_type::Absent::Untyped));
        };
        self.called_type(frame, bound.node)
    }

    /// The type the call `written` returns under `frame`, as the function it
    /// calls wrote it: `A` of the function's result `-F A`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node of `A` when `written` calls a name resolving, under
    ///   `frame`, to a function declared with as many parameters as the call
    ///   passes and a written result `-F A`, read through parentheses; the
    ///   untyped absence otherwise.
    /// - provides: the record layout of a call's result to a match on it, so a
    ///   pattern splits the record a quasi-inverse or an equivalence
    ///   abbreviates as it does at a parameter written with one.
    /// - fails: the callee's resolution refusals;
    ///   [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] reading its forms.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::ran_type`] and [`Self::scrutinee_type`].
    /// - witness: `lower::identity::tests::a_run_binder_splits_the_relation_its_call_returns_656`
    /// - witness: `lower::native::tests::a_call_as_the_scrutinee_splits_the_record_it_returns_1141`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| match *found {
        Maybe::Present(node) => node != written,
        Maybe::Absent(absent) => absent == binder_type::Absent::Untyped,
    }))]
    fn called_type(
        &mut self,
        frame: Frame,
        written: NodeIndex,
    ) -> Result<Maybe<NodeIndex, binder_type::Absent>, LoweringRefusal<'source>>
    {
        let untyped = Maybe::Absent(binder_type::Absent::Untyped);
        let Maybe::Present(call) = self.unwrapped(written)?
        else {
            return Ok(untyped);
        };
        let (Former::Call, Some((&head, arguments))) = (call.former, call.operands.split_first())
        else {
            return Ok(untyped);
        };
        // The call may be read before the walk reaches it, as a scrutinee is,
        // so its head takes its owner here: a name resolves only where a
        // declaration owns it.
        self.inherit_owner(call.node);
        let Some(tree) = self.tree.node(head)
        else {
            return Ok(untyped);
        };
        let head = Placed::of(head, tree);
        if !matches!(self.form_at(head)?, Some((_, Former::Name))) {
            return Ok(untyped);
        }
        let named = Site {
            at: head,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let Maybe::Present(Resolved::Declaration { constant, .. }) =
            self.resolve_name(named, frame, self.name_at(head))?
        else {
            return Ok(untyped);
        };
        let Some(function) = self.function_of(constant)
        else {
            return Ok(untyped);
        };
        let parameters = function
            .parameters
            .end
            .saturating_sub(function.parameters.start);
        let (Maybe::Present(result), true) = (function.result, parameters == arguments.len())
        else {
            return Ok(untyped);
        };
        if let Maybe::Present(returner) = self.unwrapped(result)?
            && returner.former == Former::ReturnerType
            && let [returned] = *returner.operands.as_slice()
        {
            return Ok(Maybe::Present(returned));
        }
        Ok(untyped)
    }

    /// The zone braces at a type's root are read in over `entries`: the session
    /// select or offer when every entry is a session form.
    ///
    /// # Specification
    /// - requires: `entries` are the type entries of the form at `site`.
    /// - ensures: the session zone when there is an entry and every one is a
    ///   session form, as [`Self::type_zone`] reads one; the ordinary zone when
    ///   none is.
    /// - fails: a misplaced tile at the first session entry of a form mixing
    ///   them with other types; a nested form's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::UnknownMold`]
    /// and [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same braces over value types, over session types,
    ///   over braces of session types, and mixed.
    /// - witness: `lower::arity::tests::a_session_entry_reads_the_select_and_the_offer`
    #[spec(ensures: |ret| !matches!(ret, Ok(TypeZone::Session)) || !entries.is_empty())]
    fn zoned(
        &mut self,
        site: Site,
        entries: &[Entry<'source>],
    ) -> Result<TypeZone, LoweringRefusal<'source>>
    {
        let mut first = None;
        let mut sessions = 0_usize;
        for entry in entries {
            let at = entry.held.at();
            if self.type_zone(at)? == TypeZone::Session {
                sessions = sessions.saturating_add(1);
                first = first.or(Some(at));
            }
        }
        match first {
            None => Ok(TypeZone::Ordinary),
            Some(_) if sessions == entries.len() => Ok(TypeZone::Session),
            Some(at) => Err(site.fault(at.span, FormFault::MisplacedTile)),
        }
    }

    /// The zone the type at `at` is read in: the session zone for `!A. S`,
    /// `?A. S`, `end` or `mu t. S`, a parenthesised session form, or braces
    /// holding at least one entry, each a session form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the session zone exactly for the forms above; the ordinary
    ///   zone for every other form, empty parentheses and empty braces
    ///   included.
    /// - fails: a nested brace's own malformed pieces; an unknown mold; the
    ///   allowance, one step per form visited.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::UnknownMold`]
    /// and [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Termination
    /// - reason: the `while let` pops one form per round and pushes only the
    ///   entries of that form, each a strict subtree of it.
    /// - measure: the forms under `at`, each visited once.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::zoned`].
    /// - witness: `lower::arity::tests::a_session_entry_reads_the_select_and_the_offer`
    #[spec(captures: before = self.fuel.remaining, ensures: |_| self.fuel.remaining <= before)]
    fn type_zone(
        &mut self,
        at: Placed,
    ) -> Result<TypeZone, LoweringRefusal<'source>>
    {
        let mut pending = Vec::from([at]);
        let mut pieces = Pieces::new();
        while let Some(next) = pending.pop() {
            self.fuel.spend()?;
            let Some((name, former)) = self.form_at(next)?
            else {
                return Ok(TypeZone::Ordinary);
            };
            let opener = match former {
                Former::SessionType => continue,
                Former::ParenthesizedType => TileName::PAREN_OPEN,
                Former::LabelledSumType => TileName::PLUS,
                Former::LazyRecordType => TileName::AMPERSAND,
                Former::Name
                | Former::Constructor
                | Former::Hole
                | Former::Number
                | Former::Text
                | Former::Character
                | Former::TypeQuote
                | Former::Parenthesized
                | Former::Unit
                | Former::Boolean
                | Former::Thunk
                | Former::Lambda
                | Former::Block
                | Former::Return
                | Former::Exit
                | Former::Become
                | Former::Loop
                | Former::While
                | Former::For
                | Former::Break
                | Former::Continue
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
                | Former::Binary
                | Former::Unary
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
                | Former::ValueFunctionType
                | Former::StaticAbstraction
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
                | Former::Instantiation
                | Former::Action
                | Former::Offer
                | Former::Access
                | Former::World
                | Former::WorldDeclaration
                | Former::Reserved(_)
                | Former::Unadmitted(_)
                | Former::Misplaced => return Ok(TypeZone::Ordinary),
            };
            read_pieces(self.pbg, self.tree, next.node, &mut pieces)?;
            if let Maybe::Present(repaired) = pieces.repair {
                return Err(repaired.refusal(name));
            }
            let nested = Site {
                at: next,
                name,
                reading: Reading::ValueType(Frame::Outermost),
            };
            let mut cursor = Cursor::new(&pieces.pieces, next.span);
            closed(nested, &mut cursor, opener)?;
            if opener == TileName::PAREN_OPEN {
                let Run::One(inner) = cursor.operands()
                else {
                    return Ok(TypeZone::Ordinary);
                };
                pending.push(inner);
                continue;
            }
            closed(nested, &mut cursor, TileName::BRACE_OPEN)?;
            let entries = self.type_entries(nested, &mut cursor, TileName::BRACE_CLOSE)?;
            if entries.is_empty() {
                return Ok(TypeZone::Ordinary);
            }
            pending.extend(entries.iter().map(|entry| entry.held.at()));
        }

        Ok(TypeZone::Session)
    }

    /// Push the entries' operands onto the operand store, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stretch naming them.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every arity-shaped plan reads its entries here.
    /// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    #[spec(captures: before = self.operands.len(), ensures: |ret| ret.start == before && ret.end == self.operands.len())]
    fn stored(
        &mut self,
        entries: &[Entry<'source>],
    ) -> Stretch
    {
        let start = self.operands.len();
        self.operands
            .extend(entries.iter().map(|entry| entry.held.at().node));

        Stretch {
            start,
            end: self.operands.len(),
        }
    }

    /// The fields of labelled entries, by label, each read as `reading` and
    /// its label kept against it.
    ///
    /// # Specification
    /// - requires: every entry is labelled by name.
    /// - ensures: one field per entry, each label kept by
    ///   [`Self::label_entry`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record type and a record value over the same labels
    ///   in two orders are one record.
    /// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
    #[spec(ensures: |ret| ret.len() <= entries.len())]
    fn fields(
        &mut self,
        entries: &[Entry<'source>],
        reading: Reading,
    ) -> BTreeMap<FieldLabel, NodeIndex>
    {
        let mut fields = BTreeMap::new();
        for entry in entries {
            if let Key::Label(name, _) = entry.key {
                let at = entry.held.at().node;
                self.read(at, reading);
                self.label_entry(entry, reading);
                let _first = fields.insert(FieldLabel::from(String::from(name.as_ref())), at);
            }
        }

        fields
    }

    /// Keep the label of `entry`, whose held node is read as `reading`, so
    /// the label answers what its entry lowers to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a label written apart from what it holds is kept, read as a
    ///   type under its frame where `reading` reads a type and as a term
    ///   otherwise; a punned field, whose label is its term, and an unlabelled
    ///   entry keep nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Lowerer::record_labels`].
    /// - witness: `lower::arity::tests::each_label_names_what_it_labels`
    #[spec(captures: before = self.labels.len(), ensures: self.labels.len() <= before.saturating_add(1))]
    pub(super) fn label_entry(
        &mut self,
        entry: &Entry<'source>,
        reading: Reading,
    )
    {
        let Key::Label(_, written) = entry.key
        else {
            return;
        };
        let held = entry.held.at();
        if held.node == written.node {
            return;
        }
        let read = match reading {
            Reading::ValueType(frame) => LabelRead::ValueType(frame),
            Reading::CompType(frame) | Reading::Result(frame) => LabelRead::CompType(frame),
            Reading::Value(_) | Reading::Computation(_) | Reading::Head(_) => LabelRead::Term,
            Reading::Unread | Reading::Function => return,
        };
        self.labelled(written.span, held.node, read);
    }

    /// Classify a telescope type, `#{A, …}` or `#{l : A, …}`.
    ///
    /// # Specification
    /// - requires: `site` is a telescope type in type position.
    /// - ensures: positional entries plan the product of their types, of any
    ///   arity, each read as a value type under the form's frame; labelled
    ///   entries plan the type over their labels, every label but the last
    ///   binding a frame extending the one before it, each entry's type read as
    ///   a value type under the frames of the labels before it and its label
    ///   kept by [`Self::label_entry`] at that frame.
    /// - fails: the wrong-sort refusal where no value type is read; the
    ///   entries' and the labels' own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The telescope's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit, one component, three, a record in two
    ///   orders, and a type over labels whose later entry names an earlier one,
    ///   each asserted as the exact core type.
    /// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    /// - witness: `lower::arity::tests::a_later_label_reading_an_earlier_one_lowers_to_nested_pairs`
    /// - witness: `lower::arity::tests::each_label_names_what_it_labels`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Product(_) | Plan::RecordType(..)))))]
    pub(super) fn telescope_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        closed(site, &mut cursor, TileName::RECORD)?;
        let entries = self.type_entries(site, &mut cursor, TileName::BRACE_CLOSE)?;
        let plan = match arrange(site, entries)? {
            Arranged::Positional(entries) => {
                let components = self.stored(&entries);
                for entry in &entries {
                    self.read(entry.held.at().node, Reading::ValueType(frame));
                }
                Plan::Product(components)
            },
            Arranged::Labelled(entries) => {
                let Some((last, binding)) = entries.split_last()
                else {
                    return Err(site.fault(site.at.span, FormFault::MissingOperand));
                };
                let links = self.named_later(&entries)?;
                let mut fields = BTreeMap::new();
                let start = self.parameters.len();
                let mut inner = frame;
                for (entry, &Dependent(linked)) in binding.iter().zip(&links) {
                    let Key::Label(name, key) = entry.key
                    else {
                        continue;
                    };
                    let declared = entry.held.at();
                    self.read(declared.node, Reading::ValueType(inner));
                    self.label_entry(entry, Reading::ValueType(inner));
                    let _first =
                        fields.insert(FieldLabel::from(String::from(name.as_ref())), declared.node);
                    let extended = self.scope.extend_typed(
                        inner,
                        name,
                        declared.node,
                        Maybe::Present(key.span),
                    );
                    if linked {
                        self.scope.mention(extended);
                    }
                    self.parameters.push(Parameter {
                        binder: key.node,
                        frame: extended,
                        declared: Maybe::Present(declared.node),
                    });
                    inner = Frame::Inner(extended);
                }
                let declared = last.held.at();
                self.read(declared.node, Reading::ValueType(inner));
                self.label_entry(last, Reading::ValueType(inner));
                let labelled = if let Key::Label(name, key) = last.key {
                    let _first =
                        fields.insert(FieldLabel::from(String::from(name.as_ref())), declared.node);
                    Some(key.node)
                }
                else {
                    None
                };
                Plan::RecordType(
                    fields,
                    Stretch {
                        start,
                        end: self.parameters.len(),
                    },
                    declared.node,
                    labelled,
                )
            },
        };
        self.plan(site, plan);

        Ok(())
    }

    /// Classify a sum over labels, `+{A, …}` or `+{l : A, …}`.
    ///
    /// # Specification
    /// - requires: `site` is a sum over labels in type position.
    /// - ensures: braces whose every entry is a session form are the select,
    ///   read whole as a session type; otherwise the sum of its entries' types
    ///   in written order, the labels erased, each read as a value type under
    ///   the form's frame.
    /// - fails: the wrong-sort refusal where no value type is read; a misplaced
    ///   entry where session forms and other types mix; the entries' and the
    ///   labels' own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The sum's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty sum, a positional and a labelled sum.
    /// - witness: `lower::arity::tests::a_sum_over_labels_lowers_to_the_sum_of_its_entries`
    /// - witness: `lower::arity::tests::a_session_entry_reads_the_select_and_the_offer`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Sum(_) | Plan::Session(..)))))]
    pub(super) fn labelled_sum_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        closed(site, &mut cursor, TileName::PLUS)?;
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let entries = self.type_entries(site, &mut cursor, TileName::BRACE_CLOSE)?;
        if self.zoned(site, &entries)? == TypeZone::Session {
            return self.session_type(Site {
                name: FormName::SELECT_SESSION_TYPE,
                ..site
            });
        }
        let frame = self.require(site, Produced::ValueType)?;
        let (Arranged::Positional(entries) | Arranged::Labelled(entries)) = arrange(site, entries)?;
        let summands = self.stored(&entries);
        for entry in &entries {
            self.read(entry.held.at().node, Reading::ValueType(frame));
            self.label_entry(entry, Reading::ValueType(frame));
        }
        self.plan(site, Plan::Sum(summands));

        Ok(())
    }

    /// Classify a lazy record over labels, `&{C, …}` or `&{l : C, …}`.
    ///
    /// # Specification
    /// - requires: `site` is a lazy record over labels in type position.
    /// - ensures: braces whose every entry is a session form are the offer,
    ///   read whole as a session type; otherwise the lazy product of its
    ///   entries, of any number, each read as a computation type under the
    ///   form's frame.
    /// - fails: the wrong-sort refusal where no computation type is read; a
    ///   misplaced entry where session forms and other types mix; the entries'
    ///   and the labels' own refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The lazy record's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — none, one, two and three entries.
    /// - witness: `lower::arity::tests::a_lazy_record_lowers_to_one_lazy_product`
    /// - witness: `lower::arity::tests::a_session_entry_reads_the_select_and_the_offer`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Session(..) | &Plan::With(_))))]
    pub(super) fn lazy_record_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        closed(site, &mut cursor, TileName::AMPERSAND)?;
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let entries = self.type_entries(site, &mut cursor, TileName::BRACE_CLOSE)?;
        if self.zoned(site, &entries)? == TypeZone::Session {
            return self.session_type(Site {
                name: FormName::OFFER_SESSION_TYPE,
                ..site
            });
        }
        let frame = self.require(site, Produced::CompType)?;
        let (Arranged::Positional(entries) | Arranged::Labelled(entries)) = arrange(site, entries)?;
        let components = self.stored(&entries);
        for entry in &entries {
            self.read(entry.held.at().node, Reading::CompType(frame));
            self.label_entry(entry, Reading::CompType(frame));
        }
        self.plan(site, Plan::With(components));

        Ok(())
    }

    /// Classify a telescope value, `#{a, …}`, `#{.l = a, …}` or `#{l = a,
    /// …}`, or the update `#{e | l = a, …}`.
    ///
    /// # Specification
    /// - requires: `site` is a telescope value in term position.
    /// - ensures: positional entries, in index order, plan the tuple of their
    ///   values, of any arity; labelled entries plan the record over them; an
    ///   update plans its base beside the record of the fields it writes; each
    ///   entry and an update's base is read as a value under the form's frame.
    /// - fails: the wrong-sort refusal where no value is read; the entries' and
    ///   the labels' own refusals, an update's field written twice among them.
    /// - panics: none.
    ///
    /// # Errors
    /// The telescope's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit, one, three, reordered indices, a record by
    ///   dotted labels and by the shorthand, each asserted as the exact core
    ///   value.
    /// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
    /// - witness: `lower::arity::tests::a_record_update_lowers_to_its_base_and_its_fields`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&(Plan::Tuple(_) | Plan::Record(_) | Plan::RecordUpdate(..)))))]
    pub(super) fn telescope(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        closed(site, &mut cursor, TileName::RECORD)?;
        let entries = if let Maybe::Present(_) = cursor.at(TileName::DOT) {
            self.dotted_entries(site, &mut cursor, TileName::EQUALS)?
        }
        else {
            match self.hole_entries(site, &mut cursor)? {
                Telescoped::Entries(entries) => entries,
                Telescoped::Update(base, written) => {
                    let Arranged::Labelled(written) = arrange(site, written)?
                    else {
                        return Err(site.fault(base.span, FormFault::MisplacedTile));
                    };
                    self.read(base.node, Reading::Value(frame));
                    let fields = self.fields(&written, Reading::Value(frame));
                    self.plan(site, Plan::RecordUpdate(base.node, fields));
                    return Ok(());
                },
            }
        };
        let plan = match arrange(site, entries)? {
            Arranged::Positional(entries) => {
                let members = self.stored(&entries);
                for entry in &entries {
                    self.read(entry.held.at().node, Reading::Value(frame));
                }
                Plan::Tuple(members)
            },
            Arranged::Labelled(entries) => {
                Plan::Record(self.fields(&entries, Reading::Value(frame)))
            },
        };
        self.plan(site, plan);

        Ok(())
    }

    /// The entries of the type over labels `former` the type at `node`
    /// states, read through parentheses and, when `thunked`, one `+U`.
    ///
    /// # Specification
    /// - requires: `node` is a type's syntax node.
    /// - ensures: the stated form's entries in written order, as
    ///   [`Self::stated_form`] reads them; nothing when the type, so read, is
    ///   another former.
    /// - fails: as [`Self::stated_form`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::stated_form`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stated_form`].
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::BudgetExceeded { .. } | LoweringRefusal::MalformedForm { .. } | LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn stated_entries(
        &mut self,
        site: Site,
        node: NodeIndex,
        former: Former,
        thunked: Thunked,
    ) -> Result<Maybe<Vec<Entry<'source>>, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        Ok(self
            .stated_form(site, node, former, thunked)?
            .map(|(_form, entries)| entries))
    }

    /// The type over labels `former` the type at `node` states, read through
    /// parentheses and, when `thunked`, one `+U`: its own node and its
    /// entries. A sum chain `A + B + …` states the labelled sum `+{A, B, …}`,
    /// a product chain `A * B * …` the telescope `#{A, B, …}`, and a lazy
    /// product chain `C & D & …` the lazy record `&{C, D, …}`.
    ///
    /// # Specification
    /// - requires: `node` is a type's syntax node.
    /// - ensures: the stated form's node and its entries in written order, a
    ///   sum chain read for a labelled sum, a product chain read for a
    ///   telescope and a lazy product chain read for a lazy record answering
    ///   their components as positional entries, as [`Self::links`] reads them;
    ///   nothing when the type, so read, is another former.
    /// - fails: [`LoweringRefusal::BudgetExceeded`]; the stated form's own
    ///   malformation, at the stated form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`],
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Termination
    /// Every round descends to a child of the finite tree and spends one step
    /// of the allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an injection under an annotation, a match over a
    ///   parameter, a match over a parameter stated as a sum chain, a copattern
    ///   block under its function's result, an observation of a thunked
    ///   parameter, by label and by position under a lazy product chain, and a
    ///   selection off a dependent record each read their labels here.
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    /// - witness: `lower::arity::tests::an_observation_projects_its_entry`
    /// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    /// - witness: `lower::native::tests::sum_patterns_case_on_the_stated_arity`
    /// - witness: `lower::native::tests::a_sum_pattern_reads_a_sum_stated_as_a_chain_791`
    /// - witness: `lower::arity::tests::an_observation_reads_through_one_thunk_only`
    /// - witness: `lower::arity::tests::an_observation_by_position_projects_its_entry_941`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(LoweringRefusal::BudgetExceeded { .. } | LoweringRefusal::MalformedForm { .. } | LoweringRefusal::UnknownMold { .. })))]
    pub(super) fn stated_form(
        &mut self,
        site: Site,
        node: NodeIndex,
        former: Former,
        thunked: Thunked,
    ) -> Result<
        Maybe<(NodeIndex, Vec<Entry<'source>>), stated_labels::Absent>,
        LoweringRefusal<'source>,
    >
    {
        let mut at = node;
        let mut through = thunked;
        let mut scratch = core::mem::take(&mut self.scratch);
        let found = loop {
            if let Err(refusal) = self.fuel.spend() {
                break Err(refusal);
            }
            let Some(tree) = self.tree.node(at)
            else {
                break Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
            };
            let placed = Placed::of(at, tree);
            let (name, held) = match self.form_at(placed) {
                Ok(Some(form)) => form,
                Ok(None) => break Ok(Maybe::Absent(stated_labels::Absent::Otherwise)),
                Err(refusal) => break Err(refusal),
            };
            if let Err(refusal) = read_pieces(self.pbg, self.tree, at, &mut scratch) {
                break Err(refusal);
            }
            if let Maybe::Present(repaired) = scratch.repair {
                break Err(repaired.refusal(name));
            }
            let stated = Site {
                at: placed,
                name,
                ..site
            };
            let mut cursor = Cursor::new(&scratch.pieces, placed.span);
            if held == former {
                let opened = if former == Former::TelescopeType {
                    closed(stated, &mut cursor, TileName::RECORD)
                }
                else {
                    let opener = if former == Former::LabelledSumType {
                        TileName::PLUS
                    }
                    else {
                        TileName::AMPERSAND
                    };
                    closed(stated, &mut cursor, opener)
                        .and_then(|()| closed(stated, &mut cursor, TileName::BRACE_OPEN))
                };
                break opened
                    .and_then(|()| self.type_entries(stated, &mut cursor, TileName::BRACE_CLOSE))
                    .map(|entries| Maybe::Present((at, entries)));
            }
            let chain = match (held, former) {
                (Former::SumType, Former::LabelledSumType) => Some(Former::SumType),
                (Former::ProductType, Former::TelescopeType) => Some(Former::ProductType),
                (Former::LazyProductType, Former::LazyRecordType) => Some(Former::LazyProductType),
                _ => None,
            };
            if let Some(link) = chain {
                break self
                    .links(stated, at, link)
                    .map(|entries| Maybe::Present((at, entries)));
            }
            let inner = if held == Former::ParenthesizedType {
                let _open = cursor.tile(TileName::PAREN_OPEN);
                let run = cursor.operands();
                match (run, cursor.at(TileName::PAREN_CLOSE)) {
                    (Run::One(inner), Maybe::Present(_)) => Some(inner),
                    (Run::Empty(_) | Run::Several { .. } | Run::One(_), _) => None,
                }
            }
            else if held == Former::ThunkType && through.0 {
                through = Thunked(false);
                scratch.pieces.iter().rev().find_map(|piece| match *piece {
                    Piece::Operand(inner) => Some(inner),
                    Piece::Tile { .. } => None,
                })
            }
            else {
                None
            };
            let Some(inner) = inner
            else {
                break Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
            };
            at = inner.node;
        };
        self.scratch = scratch;

        found
    }

    /// The codata family the type at `node` applies, read through parentheses
    /// and, when `thunked`, one `+U`.
    ///
    /// # Specification
    /// - requires: `node` is a type's syntax node, read under `frame`.
    /// - ensures: the declaration the type's head names when the type, so read,
    ///   is a family bare or applied whose head a declaration answers; nothing
    ///   for any other type.
    /// - fails: [`LoweringRefusal::BudgetExceeded`]; the type's own
    ///   malformation; the head's resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// Every round descends to a child of the finite tree and spends one step
    /// of the allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stated_observations`], and the result an
    ///   observation of a stream writes, read for the next link of a chain.
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    /// - witness: `lower::arity::tests::a_chain_of_observations_projects_each_link_1106`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| !matches!(*found, Maybe::Present(constant) if self.collected.slots.get(usize::from(constant)).is_none())))]
    fn stated_family(
        &mut self,
        site: Site,
        (node, frame): (NodeIndex, Frame),
        thunked: Thunked,
    ) -> Result<Maybe<ConstantIndex, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        let mut at = node;
        let mut through = thunked;
        let mut scratch = core::mem::take(&mut self.scratch);
        let head = loop {
            if let Err(refusal) = self.fuel.spend() {
                break Err(refusal);
            }
            let Some(tree) = self.tree.node(at)
            else {
                break Ok(None);
            };
            let placed = Placed::of(at, tree);
            let held = match self.form_at(placed) {
                Ok(Some((_, held))) => held,
                Ok(None) => break Ok(None),
                Err(refusal) => break Err(refusal),
            };
            if held == Former::TypeHead {
                break Ok(Some(placed));
            }
            if let Err(refusal) = read_pieces(self.pbg, self.tree, at, &mut scratch) {
                break Err(refusal);
            }
            if held == Former::TypeApplication {
                break Ok(scratch.pieces.first().and_then(|piece| match *piece {
                    Piece::Tile { label, at } if label == TileName::TYPE_IDENTIFIER => Some(at),
                    Piece::Tile { .. } | Piece::Operand(_) => None,
                }));
            }
            let inner = if held == Former::ParenthesizedType {
                scratch.pieces.iter().find_map(|piece| match *piece {
                    Piece::Operand(inner) => Some(inner),
                    Piece::Tile { .. } => None,
                })
            }
            else if held == Former::ThunkType && through.0 {
                through = Thunked(false);
                scratch.pieces.iter().rev().find_map(|piece| match *piece {
                    Piece::Operand(inner) => Some(inner),
                    Piece::Tile { .. } => None,
                })
            }
            else {
                None
            };
            let Some(inner) = inner
            else {
                break Ok(None);
            };
            at = inner.node;
        };
        self.scratch = scratch;
        let Some(head) = head?
        else {
            return Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
        };
        let named = Site { at: head, ..site };
        let Maybe::Present(Resolved::Declaration { constant, .. }) =
            self.resolve_name(named, frame, self.name_at(head))?
        else {
            return Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
        };
        if self.collected.slots.get(usize::from(constant)).is_none() {
            return Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
        }
        Ok(Maybe::Present(constant))
    }

    /// The observation labels of the codata family the type at `node`
    /// applies, read through parentheses and, when `thunked`, one `+U`.
    ///
    /// # Specification
    /// - requires: `node` is a type's syntax node, read under `frame`.
    /// - ensures: the labels of the family's observations in declaration order
    ///   when the type, so read, is a codata family bare or applied, as
    ///   [`Self::stated_family`] reads it; nothing for any other type.
    /// - fails: as [`Self::stated_family`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a copattern block under a stream answer and an
    ///   observation of a thunked stream each read their labels here.
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |labels| !matches!(*labels, Maybe::Present(ref labels) if labels.is_empty())))]
    pub(super) fn stated_observations(
        &mut self,
        site: Site,
        written: (NodeIndex, Frame),
        thunked: Thunked,
    ) -> Result<Maybe<Vec<Name>, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        Ok(match self.stated_family(site, written, thunked)? {
            Maybe::Present(constant) => self.codata_observations(constant),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        })
    }

    /// The codata family the observation at `index` of the family declared at
    /// `constant` returns, when its written result is that family itself
    /// applied.
    ///
    /// # Specification
    /// - ensures: `constant` when the family heads the result the observation
    ///   at `index` was written with, as its description records; nothing for
    ///   another result, an index past the observations, and a declaration with
    ///   no description.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stream's tail, whose result is the stream, read for
    ///   the next link of a chain, and its head, whose result is not.
    /// - witness: `lower::arity::tests::a_chain_of_observations_projects_each_link_1106`
    #[spec(ensures: |ret| ret.is_none_or(|family| family == constant))]
    fn observed_family(
        &self,
        constant: ConstantIndex,
        Place(index): Place,
    ) -> Option<ConstantIndex>
    {
        let slot = self.collected.slots.get(usize::from(constant))?;
        let entry = self.collected.descriptions.get(&slot.introduced_by.node)?;
        // The family's own name inside its declaration names it, unresolved
        // there by the rule against an unmarked self-reference.
        let Maybe::Present(_) = entry.written.observations.get(index)?.itself
        else {
            return None;
        };
        Some(constant)
    }

    /// The observation labels of the codata family declared at `constant`,
    /// in declaration order.
    ///
    /// # Specification
    /// - ensures: the family's observation labels when `constant` declares a
    ///   codata family with at least one; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::stated_observations`].
    /// - witness: `description::tests::a_codata_declaration_lowers_to_its_signature`
    #[spec(ensures: |ret| !matches!(ret, Maybe::Present(ref labels) if labels.is_empty()))]
    fn codata_observations(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<Vec<Name>, stated_labels::Absent>
    {
        self.collected
            .slots
            .get(usize::from(constant))
            .and_then(|slot| self.collected.descriptions.get(&slot.introduced_by.node))
            .filter(|entry| {
                entry.description.polarity == DeclPolarity::Codata
                    && !entry.description.ctors.is_empty()
            })
            .map_or(Maybe::Absent(stated_labels::Absent::Otherwise), |entry| {
                Maybe::Present(
                    entry
                        .description
                        .ctors
                        .iter()
                        .map(|observation| observation.name.clone())
                        .collect(),
                )
            })
    }

    /// The components of the chain of `link` at `chain`, `A + B + …`, `A * B *
    /// …` or `C & D & …`, as the positional entries of the labelled sum `+{A,
    /// B, …}`, the telescope `#{A, B, …}` or the lazy record `&{C, D, …}` it
    /// is.
    ///
    /// # Specification
    /// - requires: `chain` is a syntax node of `link`, a sum, a product or a
    ///   lazy product chain, read at `site`.
    /// - ensures: one positional entry per component in written order, each
    ///   unparenthesized link of the chain followed as the chain's own
    ///   classification follows it, so a parenthesized chain is one component.
    /// - fails: [`LoweringRefusal::BudgetExceeded`]; a link's own malformation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`],
    /// [`LoweringRefusal::MalformedForm`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Termination
    /// Each round spends one step of the allowance and replaces one link of
    /// the finite tree by its two operands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over a parameter stated as a sum chain of two
    ///   and of three, one summand a parenthesized sum, and as a product chain
    ///   holding a sum chain, cases on the arity the braced spelling states.
    /// - witness: `lower::native::tests::a_sum_pattern_reads_a_sum_stated_as_a_chain_791`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entries| entries.iter().all(|entry| matches!((entry.key, entry.held), (Key::Positional, Held::Operand(_))))))]
    fn links(
        &mut self,
        site: Site,
        chain: NodeIndex,
        link: Former,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let mut entries = Vec::new();
        let mut pending = Vec::from([chain]);
        while let Some(operand) = pending.pop() {
            self.fuel.spend()?;
            if let Some([first, second]) = self.chained(site, operand, link)? {
                pending.extend([second, first]);
            }
            else if let Some(node) = self.tree.node(operand) {
                entries.push(Entry {
                    key: Key::Positional,
                    held: Held::Operand(Placed::of(operand, node)),
                });
            }
        }

        Ok(entries)
    }

    /// The index and the entry the label `name`, written at `written`, names
    /// among `stated`.
    ///
    /// # Specification
    /// - requires: `stated` are a stated type's entries.
    /// - ensures: the first entry so labelled, with its index.
    /// - fails: the unresolved-name refusal at `written` when none is.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a label the stated type has and one it lacks.
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(place, _)| place.0 < stated.len()))]
    pub(super) fn labelled_in(
        stated: &[Entry<'source>],
        name: SurfaceName<'source>,
        written: Placed,
    ) -> Result<(Place, Entry<'source>), LoweringRefusal<'source>>
    {
        stated
            .iter()
            .enumerate()
            .find(|&(_, entry)| matches!(entry.key, Key::Label(held, _) if held == name))
            .map(|(index, &entry)| (Place(index), entry))
            .ok_or(LoweringRefusal::UnresolvedName {
                span: written.span,
                name,
            })
    }

    /// Classify an injection, `+{ .l = v }`.
    ///
    /// # Specification
    /// - requires: `site` is an injection in term position.
    /// - ensures: the injection of its value, read under the form's frame, into
    ///   the summand its index names, or its label names among the entries of
    ///   the sum its annotation states.
    /// - fails: the wrong-sort refusal where no value is read; the unannotated
    ///   refusal for a label with no annotation stating a sum; the
    ///   unresolved-name refusal for a label the sum does not have; the tiles'
    ///   and the hole's own faults.
    /// - panics: none.
    ///
    /// # Errors
    /// The injection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an index past the binary sum, a label under an
    ///   annotation, a label without one, and a label the sum lacks.
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Injection(..))))]
    pub(super) fn injection(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        closed(site, &mut cursor, TileName::PLUS)?;
        closed(site, &mut cursor, TileName::BRACE_OPEN)?;
        let key = self.dotted(site, &mut cursor)?;
        closed(site, &mut cursor, TileName::EQUALS)?;
        let body = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::BRACE_CLOSE)?;
        exhausted(site, &cursor)?;
        let summand = match key {
            Key::Index(index, ..) => index,
            Key::Label(name, written) => {
                let Some(&annotation) = self.classifiers.get(&site.at.node)
                else {
                    return Err(site.out(FragmentBoundary::Unannotated));
                };
                let Maybe::Present(stated) =
                    self.stated_entries(site, annotation, Former::LabelledSumType, Thunked(false))?
                else {
                    return Err(site.out(FragmentBoundary::Unannotated));
                };
                Self::labelled_in(&stated, name, written)?.0.0
            },
            Key::Positional => return Err(site.fault(body.span, FormFault::MisplacedTile)),
        };
        self.read(body.node, Reading::Value(frame));
        self.plan(site, Plan::Injection(Summand::from(summand), body.node));

        Ok(())
    }

    /// Classify a copattern block, `&{ .l => c, … }`, or the bundle
    /// `co { l = c, … }` that spells the same lazy record over bare labels.
    ///
    /// # Specification
    /// - requires: `site` is a copattern block in term position.
    /// - ensures: the lazy product of its clauses, of any number, in index
    ///   order, or in the order of the labels of the lazy record its answer
    ///   states; each clause read as a computation under the form's frame,
    ///   answering the stated entry's type when one is stated, and opened as a
    ///   body of its own, so an exit in it leaves the clause.
    /// - fails: the wrong-sort refusal where no computation is read; the
    ///   unannotated refusal for labelled clauses with no stated lazy record;
    ///   the unresolved-name refusal for a label the stated type lacks; a
    ///   missing operand at the closer for a label it has and the block does
    ///   not; the entries' and the labels' own refusals;
    ///   [`LoweringRefusal::Unreachable`] as a body.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — positional clauses, labelled clauses written out of
    ///   the stated order, labelled clauses with no answer, one clause and
    ///   none.
    /// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_answer`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&Plan::Copattern(_))))]
    pub(super) fn copattern(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let entries = if let Maybe::Present(_) = cursor.tile(TileName::CO) {
            closed(site, &mut cursor, TileName::BRACE_OPEN)?;
            self.bundle_entries(site, &mut cursor)?
        }
        else {
            closed(site, &mut cursor, TileName::AMPERSAND)?;
            closed(site, &mut cursor, TileName::BRACE_OPEN)?;
            self.dotted_entries(site, &mut cursor, TileName::FAT_ARROW)?
        };
        let answer = self.answers.get(&site.at.node).copied();
        let stated = match answer {
            Some(answer) => {
                self.stated_entries(site, answer.node, Former::LazyRecordType, Thunked(false))?
            },
            None => Maybe::Absent(stated_labels::Absent::Otherwise),
        };
        let clauses: Vec<(Entry<'source>, Option<NodeIndex>)> = match arrange(site, entries)? {
            Arranged::Positional(clauses) => {
                let typed = match stated {
                    Maybe::Present(ref stated) if stated.len() == clauses.len() => stated
                        .iter()
                        .map(|entry| Some(entry.held.at().node))
                        .collect(),
                    Maybe::Present(_) | Maybe::Absent(_) => alloc::vec![None; clauses.len()],
                };
                clauses.into_iter().zip(typed).collect()
            },
            Arranged::Labelled(clauses) => match stated {
                Maybe::Present(stated) => Self::stated_clauses(site, &clauses, &stated)?,
                Maybe::Absent(_) => {
                    let observed = match answer {
                        Some(answer) => self.stated_observations(
                            site,
                            (answer.node, answer.frame),
                            Thunked(false),
                        )?,
                        None => Maybe::Absent(stated_labels::Absent::Otherwise),
                    };
                    let Maybe::Present(observed) = observed
                    else {
                        return Err(site.out(FragmentBoundary::Unannotated));
                    };
                    Self::observed_clauses(site, &clauses, &observed)?
                },
            },
        };
        let start = self.operands.len();
        for &(clause, typed) in &clauses {
            let body = clause.held.at().node;
            self.operands.push(body);
            let _first = self.cocased.insert(body);
            self.read(body, Reading::Computation(frame));
            let stated = match (answer, typed) {
                (Some(answer), Some(typed)) => {
                    let stated = Answer {
                        node: typed,
                        frame: answer.frame,
                        over: super::native::Over::Written,
                    };
                    let _first = self.answers.insert(body, stated);
                    Maybe::Present(stated)
                },
                _ => Maybe::Absent(answered::Absent::Unstated),
            };
            self.open_body(site, clause_body(body), stated)?;
        }
        self.plan(
            site,
            Plan::Copattern(Stretch {
                start,
                end: self.operands.len(),
            }),
        );

        Ok(())
    }

    /// The labelled clauses of a copattern block in the order of the entries
    /// of the lazy record its answer states, each with its entry's type.
    ///
    /// # Specification
    /// - requires: `stated` are a stated lazy record's entries.
    /// - ensures: one clause per entry, in the entries' order, with the entry's
    ///   type node.
    /// - fails: the unresolved-name refusal for a label `stated` lacks; a
    ///   missing operand at the block for a label it has and `clauses` do not;
    ///   the unannotated refusal for a positional entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::copattern`].
    /// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_answer`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |ordered| ordered.len() == stated.len()))]
    fn stated_clauses(
        site: Site,
        clauses: &[Entry<'source>],
        stated: &[Entry<'source>],
    ) -> Result<Vec<(Entry<'source>, Option<NodeIndex>)>, LoweringRefusal<'source>>
    {
        for clause in clauses {
            if let Key::Label(name, written) = clause.key {
                let _index = Self::labelled_in(stated, name, written)?;
            }
        }
        let mut ordered = Vec::with_capacity(stated.len());
        for entry in stated {
            let Key::Label(name, _) = entry.key
            else {
                return Err(site.out(FragmentBoundary::Unannotated));
            };
            let Some(&clause) = clauses
                .iter()
                .find(|clause| matches!(clause.key, Key::Label(held, _) if held == name))
            else {
                return Err(site.fault(site.at.span, FormFault::MissingOperand));
            };
            ordered.push((clause, Some(entry.held.at().node)));
        }

        Ok(ordered)
    }

    /// The labelled clauses of a copattern block in the order of the
    /// observations of the codata family its answer applies.
    ///
    /// # Specification
    /// - requires: `observed` are a codata family's observation labels.
    /// - ensures: one clause per observation, in declaration order, with no
    ///   stated type: the checker reads each against the family's observation.
    /// - fails: the unresolved-name refusal for a label no observation has; a
    ///   missing operand at the block for an observation `clauses` lack.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stream's clauses written in and out of declaration
    ///   order, and a clause naming no observation.
    /// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_codata_answer`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |ordered| ordered.len() == observed.len()))]
    fn observed_clauses(
        site: Site,
        clauses: &[Entry<'source>],
        observed: &[Name],
    ) -> Result<Vec<(Entry<'source>, Option<NodeIndex>)>, LoweringRefusal<'source>>
    {
        let known: BTreeSet<&str> = observed.iter().map(AsRef::as_ref).collect();
        for clause in clauses {
            if let Key::Label(name, written) = clause.key
                && !known.contains(name.as_ref())
            {
                return Err(LoweringRefusal::UnresolvedName {
                    span: written.span,
                    name,
                });
            }
        }
        let mut ordered = Vec::with_capacity(observed.len());
        for label in observed {
            let Some(&clause) = clauses.iter().find(
                |clause| matches!(clause.key, Key::Label(held, _) if held.as_ref() == label.as_ref()),
            )
            else {
                return Err(site.fault(site.at.span, FormFault::MissingOperand));
            };
            ordered.push((clause, None));
        }

        Ok(ordered)
    }

    /// Classify a selection `m.l` or `m.i` as an observation when `m` is a name
    /// whose written type is a thunked lazy record, a thunked lazy product
    /// chain or a thunked codata family, a call whose callee writes one of
    /// those types, unthunked, as its result, or an observation whose result
    /// is its own codata family.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: planned when the position reads a term, a value read through
    ///   the bridge from the computation the observation is, and the selection
    ///   is one link off a name whose binder or declaration was written with
    ///   the type `+U &{…}`, `+U (C & D & …)` or `+U F(…)` for a codata family
    ///   `F`: the entry or the observation the label names, or the number `i`
    ///   places, counted from zero as a copattern block's and an injection's
    ///   positions are, of the thunk the name holds, read as a value under the
    ///   form's frame; planned the same way off a call whose callee's written
    ///   result is `&{…}`, `C & D & …` or `F(…)`, and off an observation whose
    ///   written result is its own family `F(…)`, as [`Self::observed_subject`]
    ///   reads each, the operand read as the computation it runs under the
    ///   form's frame and the type's head resolved under the outermost frame;
    ///   nothing is planned otherwise.
    /// - fails: the unresolved-name refusal for a label the lazy record or the
    ///   family lacks, a label of a lazy product chain, and a position past the
    ///   last entry or observation; the name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The observation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each entry of a lazy record of three, a label it
    ///   lacks, and each observation of a stream, by label and by position;
    ///   each entry of a lazy product chain by position, and a position past
    ///   its last; a call's stream observed by label, by position and in an
    ///   operand, and a label its family lacks; a chain of observations off a
    ///   name and off a call, and one through an observation whose result is
    ///   not its family.
    /// - witness: `lower::arity::tests::an_observation_projects_its_entry`
    /// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_codata_answer`
    /// - witness: `lower::arity::tests::an_observation_by_position_projects_its_entry_941`
    /// - witness: `lower::arity::tests::an_observation_off_a_call_projects_the_run_result_1106`
    /// - witness: `lower::arity::tests::a_chain_of_observations_projects_each_link_1106`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Observe(..))))]
    pub(super) fn observation(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        if !matches!(
            site.reading,
            Reading::Computation(_) | Reading::Head(_) | Reading::Value(_)
        ) {
            return Ok(Planned(false));
        }
        let Some((target, selected)) = Self::selection_link(site, &pieces.pieces, site.at.span)
        else {
            return Ok(Planned(false));
        };
        let numbered = self.text_at(selected).as_ref().parse::<usize>().is_ok();
        let frame = site.reading.frame();
        let Some(subject) = self.observed_subject(site, frame, target)?
        else {
            return Ok(Planned(false));
        };
        let label = self.name_at(selected);
        let (entries, thunked) = match subject {
            Subject::Written(declared, thunked, _) => (
                self.stated_entries(site, declared, Former::LazyRecordType, thunked)?,
                thunked,
            ),
            Subject::Family(_) => (
                Maybe::Absent(stated_labels::Absent::Otherwise),
                Thunked(false),
            ),
        };
        let (index, count) = match entries {
            Maybe::Present(stated) => {
                let Place(index) = if numbered {
                    Self::positioned(label, selected, &stated)?
                }
                else {
                    Self::labelled_in(&stated, label, selected)?.0
                };
                (index, stated.len())
            },
            Maybe::Absent(_) => {
                let observed = match subject {
                    Subject::Written(declared, thunked, resolved) => {
                        self.stated_observations(site, (declared, resolved), thunked)?
                    },
                    Subject::Family(family) => self.codata_observations(family),
                };
                let Maybe::Present(observed) = observed
                else {
                    return Ok(Planned(false));
                };
                let index = if numbered {
                    Self::positioned(label, selected, &observed)?.0
                }
                else {
                    let Some(index) = observed
                        .iter()
                        .position(|held| held.as_ref() == label.as_ref())
                    else {
                        return Err(LoweringRefusal::UnresolvedName {
                            span: selected.span,
                            name: label,
                        });
                    };
                    index
                };
                (index, observed.len())
            },
        };
        let frame = self.require(site, Produced::Computation)?;
        let operand = if thunked.0 {
            Reading::Value(frame)
        }
        else {
            Reading::Computation(frame)
        };
        self.read(target.node, operand);
        self.plan(
            site,
            Plan::Observe(target.node, Observed { index, count }, thunked),
        );

        Ok(Planned(true))
    }

    /// The operand and the member of a selection by label, `e.l`, or by
    /// position, `e.0`.
    ///
    /// # Specification
    /// - requires: `pieces` are a projection's pieces, spanning `span`.
    /// - ensures: the operand and the member's tile when the pieces are an
    ///   operand, a dot and a name or a number; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::observation`].
    /// - witness: `lower::arity::tests::an_observation_by_position_projects_its_entry_941`
    /// - witness: `lower::arity::tests::a_chain_of_observations_projects_each_link_1106`
    #[spec(ensures: |ret| ret.is_none_or(|(target, _)| pieces.first() == Some(&Piece::Operand(target))))]
    fn selection_link(
        site: Site,
        pieces: &[Piece],
        span: ByteSpan,
    ) -> Option<(Placed, Placed)>
    {
        if let Ok(found) = Self::link(site, pieces, span) {
            return Some(found);
        }
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return None;
        };
        let (Maybe::Present(_dot), Maybe::Present(selected)) =
            (cursor.tile(TileName::DOT), cursor.tile(TileName::NUMBER))
        else {
            return None;
        };
        Some((target, selected))
    }

    /// What the operand `target` of an observation is observed at.
    ///
    /// # Specification
    /// - requires: `target` is the operand of a selection at `site`, read under
    ///   `frame`.
    /// - ensures: for a name, the type its binder or declaration was written
    ///   with, a thunk, under `frame`, a binder's type owned by the declaration
    ///   the selection belongs to; for a call, the callee's written result, as
    ///   [`Self::called_result`] reads it, a computation under the outermost
    ///   frame; for a chain of selections rooted at either, the family the last
    ///   link's observation returns when its written result is its own family,
    ///   as [`Self::observed_family`] reads it, each link observed off what the
    ///   link before it is. Nothing otherwise, and nothing for a link its
    ///   family does not have, which that link's own reading refuses.
    /// - fails: [`LoweringRefusal::BudgetExceeded`]; the root name's and the
    ///   callee's resolution refusals; a written type's own malformation.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Termination
    /// Each round of the walk down the chain descends to a child of the
    /// finite tree and spends one step of the allowance; the walk back up
    /// visits each link it collected once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::observation`].
    /// - witness: `lower::arity::tests::an_observation_projects_its_entry`
    /// - witness: `lower::arity::tests::an_observation_off_a_call_projects_the_run_result_1106`
    /// - witness: `lower::arity::tests::a_chain_of_observations_projects_each_link_1106`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none_or(|subject| match subject { Subject::Written(node, ..) => self.tree.node(node).is_some(), Subject::Family(family) => self.collected.slots.get(usize::from(family)).is_some() })))]
    fn observed_subject(
        &mut self,
        site: Site,
        frame: Frame,
        target: Placed,
    ) -> Result<Option<Subject>, LoweringRefusal<'source>>
    {
        let mut links = Vec::new();
        let mut root = target;
        let mut scratch = core::mem::take(&mut self.scratch);
        let walked = loop {
            if let Err(refusal) = self.fuel.spend() {
                break Err(refusal);
            }
            match self.form_at(root) {
                Ok(Some((_, Former::Projection))) => {},
                Ok(_) => break Ok(()),
                Err(refusal) => break Err(refusal),
            }
            if let Err(refusal) = read_pieces(self.pbg, self.tree, root.node, &mut scratch) {
                break Err(refusal);
            }
            let Some((inner, selected)) = Self::selection_link(site, &scratch.pieces, root.span)
            else {
                break Ok(());
            };
            links.push(selected);
            root = inner;
        };
        self.scratch = scratch;
        walked?;
        let mut subject = if matches!(self.form_at(root)?, Some((_, Former::Name))) {
            let named = Site {
                at: root,
                name: FormName::IDENTIFIER,
                reading: Reading::Value(frame),
            };
            let declared = match self.resolve_name(named, frame, self.name_at(root)) {
                Ok(Maybe::Present(Resolved::Binder(bound))) => {
                    // A binder's type is written in the declaration the
                    // selection belongs to, and may lie where the walk has
                    // not yet given it that owner its names resolve by.
                    if let Maybe::Present(written) = bound.declared {
                        self.own_written(written, site.at.node);
                    }
                    bound.declared
                },
                Ok(Maybe::Present(Resolved::Declaration { declared, .. })) => declared,
                Ok(Maybe::Absent(_)) => Maybe::Absent(binder_type::Absent::Untyped),
                // A chain's root is read again by the link it heads, which
                // refuses it in its own reading.
                Err(LoweringRefusal::UnresolvedName { .. }) if !links.is_empty() => {
                    return Ok(None);
                },
                Err(refusal) => return Err(refusal),
            };
            let Maybe::Present(declared) = declared
            else {
                return Ok(None);
            };
            Subject::Written(declared, Thunked(true), frame)
        }
        else {
            // A call's callee writes its result in its own declaration, at the
            // outermost frame of the source both stand in.
            let Some(result) = self.called_result(site, frame, root)?
            else {
                return Ok(None);
            };
            Subject::Written(result.node, Thunked(false), Frame::Outermost)
        };
        for selected in links.into_iter().rev() {
            let family = match subject {
                Subject::Written(declared, thunked, resolved) => {
                    self.stated_family(site, (declared, resolved), thunked)?
                },
                Subject::Family(family) => Maybe::Present(family),
            };
            let Maybe::Present(family) = family
            else {
                return Ok(None);
            };
            let Maybe::Present(labels) = self.codata_observations(family)
            else {
                return Ok(None);
            };
            let name = self.name_at(selected);
            let index = name.as_ref().parse::<usize>().map_or_else(
                |_unnumbered| {
                    labels
                        .iter()
                        .position(|held| held.as_ref() == name.as_ref())
                },
                |place| (place < labels.len()).then_some(place),
            );
            let Some(returned) = index.and_then(|index| self.observed_family(family, Place(index)))
            else {
                return Ok(None);
            };
            subject = Subject::Family(returned);
        }

        Ok(Some(subject))
    }

    /// The entry the position `name`, written at `written`, places among
    /// `among`.
    ///
    /// # Specification
    /// - requires: `name` is a number's text.
    /// - ensures: the place the number counts from zero, below the length of
    ///   `among`.
    /// - fails: the unresolved-name refusal at `written` for a number at or
    ///   past that length.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnresolvedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::observation`].
    /// - witness: `lower::arity::tests::an_observation_by_position_projects_its_entry_941`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |place| place.0 < among.len()))]
    fn positioned<Entered>(
        name: SurfaceName<'source>,
        written: Placed,
        among: &[Entered],
    ) -> Result<Place, LoweringRefusal<'source>>
    {
        name.as_ref()
            .parse::<usize>()
            .ok()
            .filter(|&place| place < among.len())
            .map(Place)
            .ok_or(LoweringRefusal::UnresolvedName {
                span: written.span,
                name,
            })
    }

    /// The entries of the type written for the operand `target` of a
    /// selection, when the operand is a name written with a telescope or a
    /// product chain.
    ///
    /// # Specification
    /// - requires: `target` is the operand of a selection at `site`.
    /// - ensures: the written type's node and its entries in written order, as
    ///   [`Self::stated_form`] reads a telescope, when `target` is a name whose
    ///   binder or declaration was written with such a type; nothing for any
    ///   other operand, for a name written with no type, or with a type of
    ///   another former.
    /// - fails: the name's own resolution refusals; the written type's own
    ///   malformation; [`LoweringRefusal::BudgetExceeded`].
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent record selected by label, and a record, a
    ///   product chain and a value with no written type selected by place.
    /// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    /// - witness: `lower::arity::tests::a_selection_by_position_reads_the_written_type_1106`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| !matches!(*found, Maybe::Present((node, _)) if self.tree.node(node).is_none())))]
    fn written_entries(
        &mut self,
        site: Site,
        target: Placed,
    ) -> Result<
        Maybe<(NodeIndex, Vec<Entry<'source>>), stated_labels::Absent>,
        LoweringRefusal<'source>,
    >
    {
        if !matches!(self.form_at(target)?, Some((_, Former::Name))) {
            return Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
        }
        let frame = site.reading.frame();
        let named = Site {
            at: target,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let declared = match self.resolve_name(named, frame, self.name_at(target))? {
            Maybe::Present(Resolved::Binder(bound)) => bound.declared,
            Maybe::Present(Resolved::Declaration { declared, .. }) => declared,
            Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped),
        };
        let Maybe::Present(declared) = declared
        else {
            return Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
        };

        self.stated_form(site, declared, Former::TelescopeType, Thunked(false))
    }

    /// Classify a selection `p.l` as a projection when `p` is a name whose
    /// written type is a type over labels.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: planned when the selection is one link off a name whose
    ///   binder or declaration was written with the type `#{l : A, …}`: the
    ///   entry the label names, the name read as a value under the form's
    ///   frame, with the stated type and the label, so the mint projects a
    ///   record by its label and a dependent record along the nesting; a label
    ///   a record lacks is projected all the same, for the checker to refuse;
    ///   nothing is planned otherwise.
    /// - fails: the unresolved-name refusal for a label a dependent record
    ///   lacks; the wrong-sort refusal where no computation is read; the name's
    ///   own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first and the last entry of a dependent record of
    ///   two and of three, and a label it lacks.
    /// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Select(..))))]
    pub(super) fn selection(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let Ok((target, selected)) = Self::link(site, &pieces.pieces, site.at.span)
        else {
            return Ok(Planned(false));
        };
        let Maybe::Present((form, stated)) = self.written_entries(site, target)?
        else {
            return Ok(Planned(false));
        };
        if !stated
            .first()
            .is_some_and(|entry| matches!(entry.key, Key::Label(..)))
        {
            return Ok(Planned(false));
        }
        let index = match Self::labelled_in(&stated, self.name_at(selected), selected) {
            Ok((Place(index), _)) => index,
            // A record no entry depends on is projected at the label, which
            // the checker refuses as a field the record lacks, as it refuses a
            // record pattern naming it; a dependent record has no nesting
            // that reaches the label.
            Err(lacked) => match self.dependent_links(&stated)? {
                Maybe::Absent(_) => stated.len(),
                Maybe::Present(_) => return Err(lacked),
            },
        };
        let label = FieldLabel::from(String::from(self.name_at(selected).as_ref()));
        let frame = self.require(site, Produced::Computation)?;
        self.read(target.node, Reading::Value(frame));
        self.plan(
            site,
            Plan::Select(
                target.node,
                Observed {
                    index,
                    count: stated.len(),
                },
                Some((form, label)),
            ),
        );

        Ok(Planned(true))
    }

    /// Classify a selection `e.l` as the field `l` of the record `e` is, where
    /// no written type states the record: a chain of selections rooted at a
    /// value's name.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading;
    ///   [`Self::selection`] planned nothing at it.
    /// - ensures: planned when the member is a name and the chain of selections
    ///   the operand is ends at a name not capitalised that a binder or a
    ///   declaration answers, with no type written when the operand is that
    ///   name itself: the field at the member's label, the operand read as a
    ///   value under the form's frame. Nothing is planned otherwise, so a
    ///   module path, a builtin namespace's member, an observation and a name
    ///   whose written type is not a record are read as before.
    /// - fails: the wrong-sort refusal where no computation is read; the head
    ///   name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a field of a definition with no signature, a field of
    ///   a field, a builtin namespace's member and a name with a written type
    ///   that is not a record.
    /// - witness: `lower::arity::tests::a_field_of_a_record_no_type_states_projects_its_label_1106`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Field(..))))]
    pub(super) fn field(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let Ok((target, selected)) = Self::link(site, &pieces.pieces, site.at.span)
        else {
            return Ok(Planned(false));
        };
        let member = self.name_at(selected);
        if !member
            .as_ref()
            .chars()
            .next()
            .is_some_and(|first| first == '_' || first.is_lowercase())
        {
            return Ok(Planned(false));
        }
        let mut head = target;
        let mut chain = Pieces::new();
        loop {
            self.fuel.spend()?;
            match self.form_at(head)? {
                Some((_, Former::Projection)) => {
                    read_pieces(self.pbg, self.tree, head.node, &mut chain)?;
                    if let Maybe::Present(_) = chain.repair {
                        return Ok(Planned(false));
                    }
                    let Ok((inner, _)) = Self::link(site, &chain.pieces, head.span)
                    else {
                        return Ok(Planned(false));
                    };
                    head = inner;
                },
                Some((_, Former::Name)) => break,
                Some(_) | None => return Ok(Planned(false)),
            }
        }
        let name = self.name_at(head);
        if name.as_ref().chars().next().is_none_or(char::is_uppercase) {
            return Ok(Planned(false));
        }
        // The head lies under links the walk has not reached: it resolves by
        // the declaration the selection belongs to.
        self.own_written(head.node, site.at.node);
        let frame = site.reading.frame();
        let named = Site {
            at: head,
            name: FormName::IDENTIFIER,
            reading: Reading::Value(frame),
        };
        let declared = match self.resolve_name(named, frame, name)? {
            Maybe::Present(Resolved::Binder(bound)) => bound.declared,
            Maybe::Present(Resolved::Declaration { declared, .. }) => declared,
            Maybe::Absent(_) => return Ok(Planned(false)),
        };
        // A name with a written type that is no record keeps its reading.
        if head.node == target.node && matches!(declared, Maybe::Present(_)) {
            return Ok(Planned(false));
        }
        let label = FieldLabel::from(String::from(member.as_ref()));
        let frame = self.require(site, Produced::Computation)?;
        self.read(target.node, Reading::Value(frame));
        self.plan(site, Plan::Field(target.node, label));

        Ok(Planned(true))
    }

    /// Classify a selection by position, `e.0`, `e.1`, `e.2` and on, as a
    /// projection of the entry at that place.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: planned when the selected member is a number. When the
    ///   operand is a name written with a telescope or a product chain, as
    ///   [`Self::written_entries`] reads it, the entry at that place: by its
    ///   label when it has one, so a record is projected at the label and a
    ///   dependent record along its nesting, and otherwise at that component of
    ///   the product. With no such type, `0` and `1` project the first and the
    ///   second component of the pair the operand is. The operand is read as a
    ///   value under the form's frame; nothing is planned for a selection by
    ///   name.
    /// - fails: the unresolved-name refusal for a place past the written type's
    ///   entries; the unadmitted refusal for a place past `1` with no written
    ///   type, and for an entry labelled by its index; the wrong-sort refusal
    ///   where no computation is read; the name's own resolution refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both places of a dependent pair, the second's type
    ///   reading the first, and a third place refused; the places of a product
    ///   chain of three and the one past it, a place of a record, and a third
    ///   place off a value with no written type.
    /// - witness: `lower::arity::tests::a_selection_by_position_projects_a_pair_401`
    /// - witness: `lower::arity::tests::a_selection_by_position_reads_the_written_type_1106`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Select(..))))]
    pub(super) fn positional(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(&pieces.pieces, site.at.span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Ok(Planned(false));
        };
        let (Maybe::Present(_dot), Maybe::Present(position)) =
            (cursor.tile(TileName::DOT), cursor.tile(TileName::NUMBER))
        else {
            return Ok(Planned(false));
        };
        let unadmitted = || site.out(FragmentBoundary::Unadmitted(Unbuilt::Projection));
        let Ok(index) = self.text_at(position).as_ref().parse::<usize>()
        else {
            return Err(unadmitted());
        };
        let (count, labelled) = match self.written_entries(site, target)? {
            Maybe::Present((form, stated)) => {
                let Some(entry) = stated.get(index)
                else {
                    return Err(LoweringRefusal::UnresolvedName {
                        span: position.span,
                        name: self.name_at(position),
                    });
                };
                let labelled = match entry.key {
                    Key::Label(label, _) => {
                        Some((form, FieldLabel::from(String::from(label.as_ref()))))
                    },
                    Key::Positional => None,
                    Key::Index(..) => return Err(unadmitted()),
                };
                (stated.len(), labelled)
            },
            // With no written type the operand is read as the pair a
            // selection by position projects, the checker refusing any other.
            Maybe::Absent(_) if index < 2_usize => (2_usize, None),
            Maybe::Absent(_) => return Err(unadmitted()),
        };
        let frame = self.require(site, Produced::Computation)?;
        self.read(target.node, Reading::Value(frame));
        self.plan(
            site,
            Plan::Select(target.node, Observed { index, count }, labelled),
        );

        Ok(Planned(true))
    }

    /// Whether each link of a type over labels binds: one answer per entry
    /// but the last, in written order, each whether a later entry names that
    /// entry's label.
    ///
    /// # Specification
    /// - requires: `typed` are the entries of a type over labels.
    /// - ensures: the links of a type some later entry of which names an
    ///   earlier label, as [`Self::named_later`] reads them; the independent
    ///   absence for a record, and the other-former absence for entries that
    ///   are not labelled.
    /// - fails: the budget refusal; the unknown-mold refusal of a node in an
    ///   entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match over a dependent record of two splits it with
    ///   its motive, one over three splits its links as they bind, and one over
    ///   a record projects its labels.
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |found| match *found {
        | Maybe::Present(ref links) => links.contains(&Dependent(true)),
        | Maybe::Absent(_) => true,
    }))]
    pub(super) fn dependent_links(
        &mut self,
        typed: &[Entry<'source>],
    ) -> Result<Maybe<Vec<Dependent>, stated_labels::Absent>, LoweringRefusal<'source>>
    {
        if !typed
            .iter()
            .all(|entry| matches!(entry.key, Key::Label(..)))
        {
            return Ok(Maybe::Absent(stated_labels::Absent::Otherwise));
        }
        let links = self.named_later(typed)?;

        Ok(if links.contains(&Dependent(true)) {
            Maybe::Present(links)
        }
        else {
            Maybe::Absent(stated_labels::Absent::Independent)
        })
    }

    /// For each entry but the last, whether a name in a later entry spells
    /// its label.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one answer per entry but the last, in written order; an entry
    ///   without a label answers no; a later entry answers yes when a node
    ///   under it is a name or a type head whose text is the label, wherever it
    ///   stands.
    /// - fails: the budget refusal, one step per node visited; the unknown-mold
    ///   refusal of a node in an entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As stated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path endpoint naming the first label links it, and
    ///   an entry naming no label leaves its link a product.
    /// - witness: `lower::native::tests::a_pattern_at_a_dependent_record_splits_it_under_its_motive`
    /// - witness: `lower::arity::tests::a_later_label_reading_an_earlier_one_lowers_to_nested_pairs`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |links| links.len() == entries.len().saturating_sub(1)))]
    fn named_later(
        &mut self,
        entries: &[Entry<'source>],
    ) -> Result<Vec<Dependent>, LoweringRefusal<'source>>
    {
        let mut links = Vec::with_capacity(entries.len().saturating_sub(1));
        let mut pending: Vec<NodeIndex> = Vec::new();
        for (position, entry) in entries.iter().enumerate() {
            if position.saturating_add(1) == entries.len() {
                break;
            }
            let Key::Label(label, _) = entry.key
            else {
                links.push(Dependent(false));
                continue;
            };
            pending.clear();
            pending.extend(
                entries
                    .iter()
                    .skip(position.saturating_add(1))
                    .map(|later| later.held.at().node),
            );
            let mut named = false;
            while let Some(node) = pending.pop() {
                self.fuel.spend()?;
                let Some(tree) = self.tree.node(node)
                else {
                    continue;
                };
                let placed = Placed::of(node, tree);
                if matches!(
                    self.form_at(placed)?,
                    Some((_, Former::Name | Former::TypeHead))
                ) && self.text_at(placed).as_ref() == label.as_ref()
                {
                    named = true;
                    break;
                }
                pending.extend(self.tree.children(node));
            }
            links.push(Dependent(named));
        }

        Ok(links)
    }

    /// Classify a value function space whose domain list names a binder: the
    /// telescope Π `(x : A, y : B(x)) => C`.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` are the operands of the value
    ///   function space at `site`, whose frame is `frame`.
    /// - ensures: planned when `domain` is a parenthesised list one of whose
    ///   entries is `k : T`: every entry binds a frame extending the one before
    ///   it, an unnamed entry's under a name no source writes, and its arrow is
    ///   dependent exactly when a later entry or the codomain names it; each
    ///   entry's type is read as a value type under the frames before it and
    ///   the codomain under all of them; nothing is planned otherwise.
    /// - fails: a duplicate definition for a name bound twice; the binder
    ///   policy's refusal; a misplaced key; a hole's own fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The telescope's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a telescope whose second type names the first binder,
    ///   a mixed one, and a binder written twice.
    /// - witness: `lower::arity::tests::a_telescope_binds_each_entry_in_the_ones_after_it`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::Telescope(..))))]
    pub(super) fn telescope_function(
        &mut self,
        site: Site,
        frame: Frame,
        domain: Placed,
        codomain: Placed,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let entries = self.domain_entries(domain, frame)?;
        if !entries
            .iter()
            .any(|entry| matches!(entry.key, Key::Label(..)))
        {
            return Ok(Planned(false));
        }
        let mut seen: BTreeMap<SurfaceName<'source>, Placed> = BTreeMap::new();
        let start = self.parameters.len();
        let mut inner = frame;
        for entry in &entries {
            let declared = entry.held.at();
            self.read(declared.node, Reading::ValueType(inner));
            self.label_entry(entry, Reading::ValueType(inner));
            let (binder, bound, written) = match entry.key {
                Key::Label(bound, key) => {
                    if let Some(&earlier) = seen.get(&bound) {
                        return Err(LoweringRefusal::DuplicateDefinition {
                            span: key.span,
                            name: bound,
                            first: earlier.span,
                        });
                    }
                    let _first = seen.insert(bound, key);
                    self.note_binder(key, bound)?;
                    (key, bound, Maybe::Present(key.span))
                },
                Key::Positional | Key::Index(..) => (
                    declared,
                    SurfaceName::from(""),
                    Maybe::Absent(binder_site::Absent::Unwritten),
                ),
            };
            let extended = self
                .scope
                .extend_typed(inner, bound, declared.node, written);
            self.parameters.push(Parameter {
                binder: binder.node,
                frame: extended,
                declared: Maybe::Present(declared.node),
            });
            inner = Frame::Inner(extended);
        }
        self.read(codomain.node, Reading::ValueType(inner));
        self.plan(
            site,
            Plan::Telescope(
                Stretch {
                    start,
                    end: self.parameters.len(),
                },
                codomain.node,
            ),
        );

        Ok(Planned(true))
    }

    /// The entries of the parenthesised domain list `domain` of a value
    /// function space under `frame`, as written.
    ///
    /// # Specification
    /// - requires: `domain` is the operand written before `=>`.
    /// - ensures: the list's entries in written order, a binder's keyed by its
    ///   label; none for a domain that is no parenthesised type or whose pieces
    ///   were repaired.
    /// - fails: a misplaced key; a hole's own fault.
    /// - panics: none.
    /// - executable: none — the entries are read off the syntax tree, which a
    ///   predicate could check only by repeating the read.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::UnknownMold`]
    /// and [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::telescope_function`].
    /// - witness: `lower::arity::tests::a_telescope_binds_each_entry_in_the_ones_after_it`
    fn domain_entries(
        &mut self,
        domain: Placed,
        frame: Frame,
    ) -> Result<Vec<Entry<'source>>, LoweringRefusal<'source>>
    {
        let Some((name, Former::ParenthesizedType)) = self.form_at(domain)?
        else {
            return Ok(Vec::new());
        };
        let list = Site {
            at: domain,
            name,
            reading: Reading::ValueType(frame),
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, domain.node, &mut scratch).and_then(|()| {
            if let Maybe::Present(_) = scratch.repair {
                return Ok(Vec::new());
            }
            let mut cursor = Cursor::new(&scratch.pieces, domain.span);
            if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
                return Ok(Vec::new());
            }
            self.type_entries(list, &mut cursor, TileName::PAREN_CLOSE)
        });
        self.scratch = scratch;

        read
    }

    /// The domains of the value function space whose domain operand is
    /// `domain`, read under `frame`: what a lambda under it binds, in order.
    ///
    /// # Specification
    /// - requires: `domain` is the operand written before `=>`.
    /// - ensures: for a domain list naming a binder, a telescope `(x : A, …)`,
    ///   the type each entry declares, left to right; otherwise the domains
    ///   [`Self::domains`] lists, left to right; nothing for a node the tree
    ///   does not hold. The operand store is left as found.
    /// - fails: the list's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::UnknownMold`]
    /// and [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda under `A => B` binds `A`, two nested under
    ///   `(A, C) => B` bind `A` then `C`, and two nested under the telescope
    ///   `(a : A, C) => B` bind `A` then `C`.
    /// - witness: `lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `lower::native::tests::a_lambda_under_a_telescope_alias_lowers_as_under_its_dependent_arrows_815`
    #[spec(
        captures: before = self.operands.len(),
        ensures: self.operands.len() == before,
    )]
    pub(super) fn alias_domains(
        &mut self,
        domain: NodeIndex,
        frame: Frame,
    ) -> Result<Option<Vec<NodeIndex>>, LoweringRefusal<'source>>
    {
        let Some(tree) = self.tree.node(domain)
        else {
            return Ok(None);
        };
        let placed = Placed::of(domain, tree);
        let entries = self.domain_entries(placed, frame)?;
        if entries
            .iter()
            .any(|entry| matches!(entry.key, Key::Label(..)))
        {
            return Ok(Some(
                entries.iter().map(|entry| entry.held.at().node).collect(),
            ));
        }
        let start = self.operands.len();
        let listed = self.domains(placed);
        let domains = self.operands.split_off(start);
        listed?;

        Ok(Some(domains))
    }

    /// The type the binder of a dependent arrow's domain `domain` declares,
    /// read under `frame`: the `A` of `(x : A) -> C`.
    ///
    /// # Specification
    /// - requires: `domain` is the operand written before `->`.
    /// - ensures: the entry's type when `domain` is a parenthesised type
    ///   holding exactly one entry, `k : A`; nothing otherwise.
    /// - fails: the list's refusal.
    /// - panics: none.
    /// - executable: none — the entry is read off the syntax tree, which a
    ///   predicate could check only by repeating the read.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`], [`LoweringRefusal::UnknownMold`]
    /// and [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda under `(a : Empty) -> C` binds `Empty`, as
    ///   one under `Empty -> C` does.
    /// - witness: `lower::native::tests::a_lambda_under_a_telescope_alias_lowers_as_under_its_dependent_arrows_815`
    pub(super) fn binder_type(
        &mut self,
        domain: NodeIndex,
        frame: Frame,
    ) -> Result<Option<NodeIndex>, LoweringRefusal<'source>>
    {
        let Some(tree) = self.tree.node(domain)
        else {
            return Ok(None);
        };
        let entries = self.domain_entries(Placed::of(domain, tree), frame)?;
        Ok(match *entries.as_slice() {
            [ref entry] if matches!(entry.key, Key::Label(..)) => Some(entry.held.at().node),
            [] | [_] | [_, _, ..] => None,
        })
    }

    /// Classify a computation arrow whose domain names its binder: the
    /// dependent arrow `(x : A) -> C`.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` are the operands of the computation
    ///   arrow at `site`, whose frame is `frame`.
    /// - ensures: planned when `domain` is a parenthesised type holding exactly
    ///   one entry, `k : T`: the binder extends `frame`, its type is read as a
    ///   value type under `frame` and the codomain as a computation type under
    ///   the binder, which mints the dependent former exactly when the codomain
    ///   names it, as a telescope entry does; nothing is planned otherwise.
    /// - fails: the binder policy's refusal; a misplaced key; a hole's own
    ///   fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The arrow's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two dependent arrows nested to the right, each naming
    ///   the binder before it, mint the same telescope the value-function alias
    ///   spells, and a binder nothing names mints the plain arrow.
    /// - witness: `lower::arity::tests::a_dependent_arrow_is_the_telescope_the_alias_abbreviates`
    #[spec(ensures: |ret| !matches!(ret, Ok(Planned(true))) || matches!(self.plans.get(site.at.node), Some(&Plan::DependentArrow(..))))]
    pub(super) fn dependent_arrow(
        &mut self,
        site: Site,
        frame: Frame,
        domain: Placed,
        codomain: Placed,
    ) -> Result<Planned, LoweringRefusal<'source>>
    {
        let Some((name, Former::ParenthesizedType)) = self.form_at(domain)?
        else {
            return Ok(Planned(false));
        };
        let list = Site {
            at: domain,
            name,
            reading: Reading::ValueType(frame),
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, domain.node, &mut scratch).and_then(|()| {
            if let Maybe::Present(_) = scratch.repair {
                return Ok(Vec::new());
            }
            let mut cursor = Cursor::new(&scratch.pieces, domain.span);
            if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
                return Ok(Vec::new());
            }
            self.type_entries(list, &mut cursor, TileName::PAREN_CLOSE)
        });
        self.scratch = scratch;
        let entries = read?;
        let &[
            Entry {
                key: Key::Label(bound, key),
                held,
            },
        ] = entries.as_slice()
        else {
            return Ok(Planned(false));
        };
        let declared = held.at();
        self.read(declared.node, Reading::ValueType(frame));
        self.labelled(key.span, declared.node, LabelRead::ValueType(frame));
        self.note_binder(key, bound)?;
        let extended =
            self.scope
                .extend_typed(frame, bound, declared.node, Maybe::Present(key.span));
        let start = self.parameters.len();
        self.parameters.push(Parameter {
            binder: key.node,
            frame: extended,
            declared: Maybe::Present(declared.node),
        });
        self.read(codomain.node, Reading::CompType(Frame::Inner(extended)));
        self.plan(
            site,
            Plan::DependentArrow(
                Stretch {
                    start,
                    end: self.parameters.len(),
                },
                codomain.node,
            ),
        );

        Ok(Planned(true))
    }

    /// Mint a type over labels: the record of its fields, or the dependent
    /// pairs nested to the right where a later entry names an earlier label.
    ///
    /// # Specification
    /// - requires: every entry's type is already minted or absent; every
    ///   mention in the entries has been recorded.
    /// - ensures: the record type over `fields` when the entries name no binder
    ///   of `binders`, as [`Self::names_own_binder`] reads them; otherwise the
    ///   last entry's type wrapped, innermost first, by one link per binder:
    ///   `Σ` over its entry's type when the entries name the binder, the eager
    ///   product of two otherwise; every node with the written origin, and each
    ///   `Σ` with where its label is written, the name its binder takes (#728),
    ///   and, where its second component is the last entry or another `Σ`,
    ///   where that entry's label is written (#1613); nothing when a type did
    ///   not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record in two orders, a dependent record of two,
    ///   and one of three whose middle label nothing names.
    /// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    /// - witness: `lower::arity::tests::a_later_label_reading_an_earlier_one_lowers_to_nested_pairs`
    /// - witness: `lower::arity::tests::each_dependent_pair_keeps_both_labels_1613`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_labelled_type(
        &self,
        fields: &BTreeMap<FieldLabel, NodeIndex>,
        binders: Stretch,
        (last, labelled): (NodeIndex, Option<NodeIndex>),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        if !bool::from(self.binds_any(binders, last)) {
            return self.mint_record_type(fields, sink, origin);
        }
        let written = stretch(&self.parameters, binders);
        let mut nested = match self.value_type_at(last) {
            Maybe::Present(nested) => nested,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        // The label the next link out reads as its second component's: the
        // last entry's, then each pair's own, while the links are pairs.
        let mut second = labelled.map(|label| self.origin_at(label));
        for parameter in written.iter().rev() {
            let Maybe::Present(declared) = parameter.declared
            else {
                return Maybe::Absent(lowered::Absent::Unstated);
            };
            let first = match self.value_type_at(declared) {
                Maybe::Present(first) => first,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            let own = self.origin_at(parameter.binder);
            nested = if bool::from(self.names_own_binder(last, parameter.frame)) {
                let id = sink.arena.value_type_sigma(first, nested);
                if let Maybe::Present(label) = own {
                    sink.origins.record_pair(id, label);
                }
                if let Some(Maybe::Present(label)) = second {
                    sink.origins.record_second(id, label);
                }
                second = Some(own);
                id
            }
            else {
                second = None;
                sink.arena.value_type_product(&[first, nested])
            };
            sink.origins.record_value_type(nested, origin);
        }

        Maybe::Present(Lowered::ValueType(nested))
    }

    /// Mint a record type over its fields.
    ///
    /// # Specification
    /// - requires: every field is already minted or absent.
    /// - ensures: the record type keyed by the fields' labels, with the written
    ///   origin; nothing when a field did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::telescope_type`].
    /// - witness: `lower::arity::tests::a_telescope_type_lowers_by_its_arity`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_record_type(
        &self,
        fields: &BTreeMap<FieldLabel, NodeIndex>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut minted = BTreeMap::new();
        for (label, &field) in fields {
            match self.value_type_at(field) {
                Maybe::Present(id) => {
                    let _first = minted.insert(label.clone(), id);
                },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_record(minted);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint a record over its fields.
    ///
    /// # Specification
    /// - requires: every field is already minted or absent.
    /// - ensures: the record keyed by the fields' labels, with the written
    ///   origin; nothing when a field did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::telescope`].
    /// - witness: `lower::arity::tests::a_telescope_value_lowers_by_its_arity`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Value(_))))]
    pub(super) fn mint_record(
        &self,
        fields: &BTreeMap<FieldLabel, NodeIndex>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut minted = BTreeMap::new();
        for (label, &field) in fields {
            match self.value_at(field) {
                Maybe::Present(id) => {
                    let _first = minted.insert(label.clone(), id);
                },
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_record(minted);

        Maybe::Present(sink.value(id, origin))
    }

    /// Mint a record update: its base, beside the record of the fields it
    /// writes.
    ///
    /// # Specification
    /// - requires: the base and every field are already minted or absent.
    /// - ensures: the update of the base by the record keyed by the fields'
    ///   labels, both with the written origin; nothing when the base or a field
    ///   did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::telescope`].
    /// - witness: `lower::arity::tests::a_record_update_lowers_to_its_base_and_its_fields`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Value(_))))]
    pub(super) fn mint_record_update(
        &self,
        base: NodeIndex,
        fields: &BTreeMap<FieldLabel, NodeIndex>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let base = match self.value_at(base) {
            Maybe::Present(id) => id,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let overlay = match self.mint_record(fields, sink, origin) {
            Maybe::Present(Lowered::Value(overlay)) => overlay,
            Maybe::Present(_) => return Maybe::Absent(lowered::Absent::OtherSort),
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let id = sink.arena.value_record_update(base, overlay);

        Maybe::Present(sink.value(id, origin))
    }

    /// Mint a sum over its summands.
    ///
    /// # Specification
    /// - requires: every summand is already minted or absent.
    /// - ensures: the sum of the summands in order, with the written origin;
    ///   nothing when a summand did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::labelled_sum_type`].
    /// - witness: `lower::arity::tests::a_sum_over_labels_lowers_to_the_sum_of_its_entries`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_sum(
        &self,
        summands: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, summands);
        let mut parts: Vec<ValueTypeId> = Vec::with_capacity(written.len());
        for &summand in written {
            match self.value_type_at(summand) {
                Maybe::Present(part) => parts.push(part),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_sum(&parts);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint an injection.
    ///
    /// # Specification
    /// - requires: the body is already minted or absent.
    /// - ensures: the injection of the body into `summand`, with the written
    ///   origin; nothing when the body did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::injection`].
    /// - witness: `lower::arity::tests::an_injection_takes_its_index_from_its_label`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Value(_))))]
    pub(super) fn mint_injection(
        &self,
        summand: Summand,
        body: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.value_at(body).map(|injected| {
            let id = sink.arena.value_injection(summand, injected);
            sink.value(id, origin)
        })
    }

    /// Mint a lazy record type: the lazy product of its entries.
    ///
    /// # Specification
    /// - requires: every entry is already minted or absent.
    /// - ensures: `With(C1, …, Cn)` in written order, of any number of entries,
    ///   with the written origin; nothing when an entry did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::lazy_record_type`].
    /// - witness: `lower::arity::tests::a_lazy_record_lowers_to_one_lazy_product`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::CompType(_))))]
    pub(super) fn mint_with(
        &self,
        entries: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, entries);
        let mut parts: Vec<CompTypeId> = Vec::with_capacity(written.len());
        for &entry in written {
            match self.comp_type_at(entry) {
                Maybe::Present(part) => parts.push(part),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let with = sink.arena.comp_type_with(&parts);
        sink.origins.record_comp_type(with, origin);

        Maybe::Present(Lowered::CompType(with))
    }

    /// Mint a copattern block: the lazy product of its clauses.
    ///
    /// # Specification
    /// - requires: every clause is already minted or absent.
    /// - ensures: `with(c1, …, cn)` in the answer's order, of any number of
    ///   clauses, each clause minted as a body with its exits where it ends,
    ///   with the written origin; nothing when a clause did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::copattern`].
    /// - witness: `lower::arity::tests::a_copattern_block_orders_its_clauses_by_its_answer`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    pub(super) fn mint_copattern(
        &self,
        clauses: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, clauses);
        let mut parts: Vec<ComputationId> = Vec::with_capacity(written.len());
        for &clause in written {
            match self.mint_body(clause_body(clause), sink, origin) {
                Maybe::Present(part) => parts.push(part),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let with = sink.arena.computation_with(&parts);
        sink.origins.record_computation(with, origin);

        Maybe::Present(Lowered::Computation(with))
    }

    /// Mint an observation: the thunk forced, or the call run, then projected
    /// at the entry it selects.
    ///
    /// # Specification
    /// - requires: the subject is already minted or absent.
    /// - ensures: `force m` projected at the selected entry's index when
    ///   `thunked`, the subject's own computation projected there otherwise,
    ///   every node with the written origin; nothing when the subject did not
    ///   lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::observation`].
    /// - witness: `lower::arity::tests::an_observation_projects_its_entry`
    /// - witness: `lower::arity::tests::an_observation_off_a_call_projects_the_run_result_1106`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    pub(super) fn mint_observe(
        &self,
        subject: NodeIndex,
        observed: Observed,
        thunked: Thunked,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let observing = if thunked.0 {
            let thunk: ValueId = match self.value_at(subject) {
                Maybe::Present(thunk) => thunk,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            let forced = sink.arena.computation_force(thunk);
            sink.origins.record_computation(forced, origin);
            forced
        }
        else {
            match self.computation_at(subject) {
                Maybe::Present(run) => run,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        };
        let projected = sink.arena.computation_project(
            gandr_kernel_term::Component::from(observed.index),
            observing,
        );
        sink.origins.record_computation(projected, origin);

        Maybe::Present(Lowered::Computation(projected))
    }

    /// Mint a selection: a record projected at the label it selects, the
    /// dependent record projected along the nesting to the entry it selects,
    /// or a product projected at the component it selects.
    ///
    /// # Specification
    /// - requires: the subject is already minted or absent; `labelled`, when
    ///   present, is the type over labels the subject is stated with and the
    ///   label selected.
    /// - ensures: with no label, the subject projected at the selected
    ///   component, since a product mints as one tuple of all its components;
    ///   when the stated type mints as a record, as [`Self::binds_any`] reads
    ///   it, the record projection at the label; otherwise the subject
    ///   projected at component one once per entry before the selected one,
    ///   each projection but the last read as the value it returns, then at
    ///   component zero unless the entry is the last; component zero of a type
    ///   of one entry; every node with the written origin; nothing when the
    ///   subject did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::selection`], a selection off a record no
    ///   field depends on, and the places of a product of three.
    /// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    /// - witness: `lower::arity::tests::a_selection_off_a_record_projects_its_label_855`
    /// - witness: `lower::arity::tests::a_selection_by_position_reads_the_written_type_1106`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::Computation(_))))]
    pub(super) fn mint_select(
        &self,
        subject: NodeIndex,
        selected: Observed,
        labelled: Option<&(NodeIndex, FieldLabel)>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let held: ValueId = match self.value_at(subject) {
            Maybe::Present(held) => held,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let Some(&(stated, ref label)) = labelled
        else {
            let id = sink.arena.computation_tuple_projection(
                held,
                gandr_kernel_term::Component::from(selected.index),
            );
            sink.origins.record_computation(id, origin);
            return Maybe::Present(Lowered::Computation(id));
        };
        let record = match self.plans.get(stated) {
            Some(&Plan::RecordType(_, binders, last, _))
                if !bool::from(self.binds_any(binders, last)) =>
            {
                Some(label)
            },
            _ => None,
        };
        Self::project(held, selected, record, sink, origin).map(Lowered::Computation)
    }

    /// Project the entry `selected` names off the record or the dependent
    /// record `held`.
    ///
    /// # Specification
    /// - requires: `held` is minted; `record`, when present, is the label of
    ///   the selected entry of a record no entry depends on.
    /// - ensures: the record projection at `record`'s label when present;
    ///   otherwise `held` projected at component one once per entry before the
    ///   selected one, each projection but the last read as the value it
    ///   returns, then at component zero unless the entry is the last;
    ///   component zero of a type of one entry; every node with `origin`.
    /// - provides: the one projection a selection and a model's carrier share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_select`], and a model's carrier read
    ///   off its nesting.
    /// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    /// - witness: `lower::arity::tests::a_selection_off_a_record_projects_its_label_855`
    /// - witness: `tests::modules::models::a_model_binder_s_carrier_is_its_projected_sort_2131`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(id) if sink.arena.computation(id).is_some()))]
    pub(super) fn project(
        mut held: ValueId,
        selected: Observed,
        record: Option<&FieldLabel>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        if let Some(label) = record {
            let id = sink
                .arena
                .computation_record_projection(held, label.clone());
            sink.origins.record_computation(id, origin);
            return Maybe::Present(id);
        }
        let mut sides = path(selected);
        if sides.is_empty() {
            sides.push(Side::Left);
        }
        let mut projected = None;
        for side in sides {
            if let Some(inner) = projected {
                held = sink.arena.value_returned(inner);
                sink.origins.record_value(held, origin);
            }
            let component = gandr_kernel_term::Component::from(match side {
                Side::Left => 0_usize,
                Side::Right => 1_usize,
            });
            let id = sink.arena.computation_tuple_projection(held, component);
            sink.origins.record_computation(id, origin);
            projected = Some(id);
        }

        projected.map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present)
    }

    /// Whether the entries of a type over labels, `binders` its written
    /// binders and `last` its last entry's type, name any of the binders: a
    /// type over labels that does mints as dependent pairs, one that does not
    /// as a record.
    ///
    /// # Specification
    /// - requires: every mention in the entries has been recorded.
    /// - ensures: whether [`Self::names_own_binder`] reads some binder of
    ///   `binders` named from `last`.
    /// - provides: the one record-or-pairs decision the type's mint and a
    ///   selection's mint share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_labelled_type`].
    /// - witness: `lower::arity::tests::a_later_label_reading_an_earlier_one_lowers_to_nested_pairs`
    #[spec(ensures: |ret| bool::from(ret) == stretch(&self.parameters, binders).iter().any(|parameter| bool::from(self.names_own_binder(last, parameter.frame))))]
    fn binds_any(
        &self,
        binders: Stretch,
        last: NodeIndex,
    ) -> Mentioned
    {
        stretch(&self.parameters, binders)
            .iter()
            .map(|parameter| self.names_own_binder(last, parameter.frame))
            .find(|&mentioned| bool::from(mentioned))
            .unwrap_or_default()
    }

    /// Mint a telescope Π: its entries' dependent arrows over the returner of
    /// its codomain, thunked.
    ///
    /// # Specification
    /// - requires: every entry's type and the codomain are already minted or
    ///   absent.
    /// - ensures: `+U (Π A1. … Π An. -F B)`, an entry's arrow dependent when
    ///   the telescope names its frame, as [`Self::names_own_binder`] reads it,
    ///   every node with the written origin; nothing when a type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::telescope_function`].
    /// - witness: `lower::arity::tests::a_telescope_binds_each_entry_in_the_ones_after_it`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::ValueType(_))))]
    pub(super) fn mint_telescope(
        &self,
        entries: Stretch,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.parameters, entries);
        let mut domains: Vec<ValueTypeId> = Vec::with_capacity(written.len());
        for parameter in written {
            let Maybe::Present(declared) = parameter.declared
            else {
                return Maybe::Absent(lowered::Absent::Unstated);
            };
            match self.value_type_at(declared) {
                Maybe::Present(domain) => domains.push(domain),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let returned = match self.value_type_at(codomain) {
            Maybe::Present(returned) => returned,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut arrow = sink.arena.comp_type_returner(returned);
        sink.origins.record_comp_type(arrow, origin);
        for (parameter, &domain) in written.iter().zip(&domains).rev() {
            arrow = if bool::from(self.names_own_binder(codomain, parameter.frame)) {
                let id = sink.arena.comp_type_pi(domain, arrow);
                if let Maybe::Present(binder) = self.origin_at(parameter.binder) {
                    sink.origins.record_arrow(id, binder);
                }
                id
            }
            else {
                sink.arena.comp_type_arrow(domain, arrow)
            };
            sink.origins.record_comp_type(arrow, origin);
        }
        let id = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Mint a dependent arrow: the Π over its one binder's type into its
    /// codomain, or the plain arrow when the codomain does not name it.
    ///
    /// # Specification
    /// - requires: the binder's type and the codomain are already minted or
    ///   absent.
    /// - ensures: `Π (x : A). C` when the codomain names the binder, as
    ///   [`Self::names_own_binder`] reads it, `A → C` otherwise, with the
    ///   written origin; nothing when a type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::dependent_arrow`].
    /// - witness: `lower::arity::tests::a_dependent_arrow_is_the_telescope_the_alias_abbreviates`
    /// - witness: `lower::tests::a_dependent_arrow_a_body_quotes_binds_what_its_codomain_names`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_) | Maybe::Present(Lowered::CompType(_))))]
    pub(super) fn mint_dependent_arrow(
        &self,
        entries: Stretch,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let Some(&Parameter {
            declared: Maybe::Present(declared),
            frame,
            binder,
            ..
        }) = stretch(&self.parameters, entries).first()
        else {
            return Maybe::Absent(lowered::Absent::Unstated);
        };
        let (domain, body) = match (self.value_type_at(declared), self.comp_type_at(codomain)) {
            (Maybe::Present(domain), Maybe::Present(body)) => (domain, body),
            (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                return Maybe::Absent(reason);
            },
        };
        let id = if bool::from(self.names_own_binder(codomain, frame)) {
            let id = sink.arena.comp_type_pi(domain, body);
            if let Maybe::Present(binder) = self.origin_at(binder) {
                sink.origins.record_arrow(id, binder);
            }
            id
        }
        else {
            sink.arena.comp_type_arrow(domain, body)
        };
        sink.origins.record_comp_type(id, origin);

        Maybe::Present(Lowered::CompType(id))
    }
}
