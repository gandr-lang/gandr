//! The records of the arity-shaped formers that the lowering's context holds.
//!
//! The classification reads a sub-record, an observation and a link of a type
//! over labels into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::Site;
use crate::by_form::FormStretch;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Placed;
use crate::form::TileName;
use crate::resolve::SurfaceName;

/// How a sub-record projects one field of the value it selects from.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a stated projection carries the entry and the type over labels
///   the value's name is written with; a field carries nothing more.
/// - executable: none — the record holds no form to check against.
///
/// # Adequacy
/// - hypothesis: L3 — a sub-record of a stated record and of a record no type
///   states, each projecting every label it names.
/// - witness: `gandr-surface-lowering::lower::arity::tests::a_sub_record_binds_each_field_and_returns_their_record`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Projection
{
    /// The entry `Observed` names of the type over labels at the node, as a
    /// selection `p.l` off a name written with that type projects it.
    Stated(Observed, NodeIndex),
    /// The field at the label of a record no written type states, for the
    /// checker to read off the record type the value synthesises.
    Field,
}

/// One field a sub-record selects: its label and how it is projected.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the label as written and its projection.
/// - executable: none — the record holds no form to check against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Projection`].
/// - witness: `gandr-surface-lowering::lower::arity::tests::a_sub_record_binds_each_field_and_returns_their_record`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Selected
{
    /// The field's label.
    pub label: FieldLabel,
    /// How the field is projected.
    pub projection: Projection,
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
/// - witness: `gandr-surface-lowering::lower::arity::tests::an_observation_projects_its_entry`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Observed
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
pub struct Thunked(pub bool);

/// Whether a link of a type over labels binds: a later entry names the
/// link's label, so the link is a `Σ` and a split of it reads the match's
/// motive at its scrutinee.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dependent(pub bool);

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
/// - witness: `gandr-surface-lowering::lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Key<'source>
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
/// - witness: `gandr-surface-lowering::lower::native::tests::telescope_patterns_split_and_project`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Held
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
    #[must_use]
    #[inline]
    pub const fn at(self) -> Placed
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
/// - witness: `gandr-surface-lowering::lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Entry<'source>
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
    #[must_use]
    #[inline]
    pub const fn keyed_at(self) -> Placed
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
/// - witness: `gandr-surface-lowering::lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Arranged<'source>
{
    /// Entries labelled by place or by index, in index order.
    Positional(Vec<Entry<'source>>),
    /// Entries labelled by name, in written order.
    Labelled(Vec<Entry<'source>>),
}

/// Whether a form was read as an arity-shaped former and planned.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Planned(pub bool);

/// A copattern clause read as a body of its own: no statements, the clause
/// its last computation.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn clause_body(clause: NodeIndex) -> Block
{
    Block {
        statements: FormStretch::default(),
        last: clause,
    }
}

/// Whether the entries of a parenthesised type are a group of outputs. One
/// unlabelled entry is no group: it groups one type.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Grouped(pub bool);

/// The place of an entry among the entries a type states, counting from
/// zero.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Place(pub usize);

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
/// - witness: `gandr-surface-lowering::lower::arity::tests::labels_are_of_one_kind_and_written_once`
#[spec(
    captures: count = entries.len(),
    ensures: |ret| ret.as_ref().map_or(true, |arranged| match *arranged {
        | Arranged::Positional(ref ordered) | Arranged::Labelled(ref ordered) => ordered.len() == count,
    }),
)]
#[inline]
pub fn arrange<'source>(
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
/// - witness: `gandr-surface-lowering::lower::arity::tests::a_telescope_value_lowers_by_its_arity`
#[spec(ensures: |ret| ret.is_err() || matches!(cursor.peek(), Maybe::Absent(_) | Maybe::Present(_)))]
#[inline]
pub fn separated<'source>(
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
