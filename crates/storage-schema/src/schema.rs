//! The schema: a finitely presented category with attributes, as a value.
//!
//! A [`Schema`] holds objects (the tables), arrows between objects (the
//! foreign keys, each a total function), attribute types, attributes (an
//! object's typed columns) and path equations between composable arrow paths.
//! A [`Presentation`] states one by name; [`Schema::present`] validates it and
//! fixes its canonical image, and [`Schema::identity`] is BLAKE3 of that image.
//!
//! # The image
//!
//! ```text
//! image     := "gandr:storage-schema:schema:v1"
//!           || section(object name)
//!           || section(attribute type name)
//!           || section(arrow)
//!           || section(attribute)
//!           || section(equation)
//! section(x) := u32le count || x*
//! name      := u32le byte length || UTF-8 bytes
//! arrow     := name || u32le source object || u32le target object || indexing
//! attribute := name || u32le object || u32le attribute type || indexing
//! equation  := name || u32le start object || path || path
//! path      := u32le length || u32le arrow*
//! indexing  := 0x00 unindexed | 0x01 indexed
//! identity  := BLAKE3(image)
//! ```
//!
//! Each section is sorted strictly by name, and an ordinal is a position in
//! its section, so a schema has exactly one image. Names are unique across
//! the whole schema: an arrow and an object never share a name, and a refusal
//! naming an element is never ambiguous. [`Schema::decode`] admits exactly the
//! images [`Schema::encode`] writes: it reads the sections back into a
//! presentation, presents it, and refuses an image that does not re-encode
//! byte for byte.
//!
//! # Identifiers
//!
//! [`ObjectId`], [`ArrowId`], [`AttributeId`], [`AttributeTypeId`] and
//! [`EquationId`] are ordinals into the schema's sorted sections. A schema is
//! immutable once presented, so an ordinal never moves; an ordinal from one
//! schema means nothing in another, and a store refuses one out of range by
//! name. Parts are never identified this way: a part's key is the stable
//! counter the store mints (the `parts` module).

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

/// The domain every schema image opens with, inside the hashed preimage.
pub const SCHEMA_DOMAIN: &[u8] = b"gandr:storage-schema:schema:v1";

/// The byte length of a [`SchemaIdentity`]: one BLAKE3 output.
pub const SCHEMA_IDENTITY_LEN: usize = 0x20_usize;

/// The name of one schema element.
///
/// A name is any nonempty UTF-8 string; [`Schema::present`] refuses the empty
/// one and a name used twice anywhere in a schema.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Name(Box<str>);

impl From<&str> for Name
{
    /// Copies a string as an element name; emptiness is refused at
    /// presentation, not here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(Box::from(text))
    }
}

impl AsRef<str> for Name
{
    /// Borrows the name's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for Name
{
    /// Writes the name's text unquoted.
    ///
    /// # Specification
    /// - ensures: writes exactly the name's text.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on the reproduced defect's refusal renders the vertex
    ///   object's name inside the message, distinguishing a substituted or
    ///   quoted name.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The BLAKE3 identity of a schema's canonical image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SchemaIdentity([u8; SCHEMA_IDENTITY_LEN]);

impl From<[u8; SCHEMA_IDENTITY_LEN]> for SchemaIdentity
{
    /// Wraps digest bytes; nothing checks that they hash an image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; SCHEMA_IDENTITY_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for SchemaIdentity
{
    /// Borrows the digest bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl fmt::Display for SchemaIdentity
{
    /// Writes the identity as lowercase hexadecimal.
    ///
    /// # Specification
    /// - ensures: writes two lowercase hexadecimal digits per byte, in byte
    ///   order, and nothing else.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on the keyed-index schema's pinned identity compares
    ///   the full sixty-four digit rendering, distinguishing reordered bytes,
    ///   dropped zero nibbles and uppercase digits.
    /// - witness: `tests::keyed::the_keyed_schema_identity_is_pinned`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

/// An object of a schema: one table, by its ordinal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ObjectId(usize);

/// An arrow of a schema: one total foreign key, by its ordinal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArrowId(usize);

/// An attribute of a schema: one typed column, by its ordinal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AttributeId(usize);

/// An attribute type of a schema, by its ordinal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AttributeTypeId(usize);

/// A path equation of a schema, by its ordinal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EquationId(usize);

impl From<ObjectId> for usize
{
    /// Reads the object's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: ObjectId) -> Self
    {
        id.0
    }
}

impl From<ArrowId> for usize
{
    /// Reads the arrow's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: ArrowId) -> Self
    {
        id.0
    }
}

impl From<AttributeId> for usize
{
    /// Reads the attribute's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: AttributeId) -> Self
    {
        id.0
    }
}

impl From<AttributeTypeId> for usize
{
    /// Reads the attribute type's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: AttributeTypeId) -> Self
    {
        id.0
    }
}

impl From<EquationId> for usize
{
    /// Reads the equation's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: EquationId) -> Self
    {
        id.0
    }
}

/// Whether a column's inverse is materialized.
///
/// An index is derived data: declaring one changes what the store maintains
/// and proves, never what the store holds.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Indexing
{
    /// No inverse is kept; a preimage question is refused.
    Unindexed,
    /// The preimage of every value is kept sorted and proved by range.
    Indexed,
}

/// Which kind of schema element a refusal names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ElementKind
{
    /// An object.
    Object,
    /// An attribute type.
    AttributeType,
    /// An arrow.
    Arrow,
    /// An attribute.
    Attribute,
    /// A path equation.
    Equation,
}

/// An ordinal a caller handed in, reported as it was given.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ordinal(pub usize);

/// Where a schema image stopped making sense.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ImageFault
{
    /// The image does not open with [`SCHEMA_DOMAIN`].
    Domain,
    /// The image ends inside a field.
    Truncated,
    /// A name is not UTF-8.
    NotUtf8,
    /// An indexing byte is neither `0x00` nor `0x01`.
    IndexingTag,
    /// An ordinal names no element of its section.
    Ordinal,
    /// Bytes follow the last section.
    Trailing,
    /// The image presents a schema whose own image differs.
    NotCanonical,
}

/// Every way a schema, its image or a lookup in it is refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SchemaError
{
    /// A schema element has the empty name.
    EmptyName,
    /// A name is used by two elements.
    DuplicateName
    {
        /// The repeated name.
        name: Name,
    },
    /// A name resolves to no element of the expected kind.
    Unknown
    {
        /// The kind the name was looked up as.
        kind: ElementKind,
        /// The name.
        name: Name,
    },
    /// An ordinal names no element of its kind.
    UnknownOrdinal
    {
        /// The kind the ordinal was looked up as.
        kind: ElementKind,
        /// The ordinal.
        ordinal: Ordinal,
    },
    /// An equation's path takes an arrow out of an object it is not at.
    NotComposable
    {
        /// The equation.
        equation: Name,
        /// The arrow that does not compose.
        arrow: Name,
        /// The object the path had reached.
        at: Name,
    },
    /// An equation's two sides end at different objects.
    EndpointsDiffer
    {
        /// The equation.
        equation: Name,
        /// Where the left side ends.
        left: Name,
        /// Where the right side ends.
        right: Name,
    },
    /// A section holds more elements than the image's `u32` counts carry.
    TooLarge
    {
        /// The section.
        kind: ElementKind,
    },
    /// A schema image is malformed.
    Image
    {
        /// Where it failed.
        fault: ImageFault,
    },
}

impl fmt::Display for SchemaError
{
    /// Writes the refusal with the names it carries.
    ///
    /// # Specification
    /// - ensures: writes one line naming the refusal and every name and ordinal
    ///   it carries.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a non-composable equation observes the equation,
    ///   arrow and object names in the message, distinguishing a dropped or
    ///   swapped payload.
    /// - witness: `tests::schema::a_path_that_does_not_compose_is_refused_by_name`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::EmptyName => f.write_str("a schema element has the empty name"),
            | Self::DuplicateName { ref name } => {
                write!(f, "the name `{name}` is used by two schema elements")
            },
            | Self::Unknown { kind, ref name } => write!(f, "no {kind} is named `{name}`"),
            | Self::UnknownOrdinal { kind, ordinal } => {
                write!(f, "no {kind} has ordinal {}", ordinal.0)
            },
            | Self::NotComposable {
                ref equation,
                ref arrow,
                ref at,
            } => write!(
                f,
                "equation `{equation}`: arrow `{arrow}` does not leave `{at}`, where its path is"
            ),
            | Self::EndpointsDiffer {
                ref equation,
                ref left,
                ref right,
            } => write!(
                f,
                "equation `{equation}`: the left side ends at `{left}`, the right at `{right}`"
            ),
            | Self::TooLarge { kind } => write!(f, "too many {kind} elements for the image"),
            | Self::Image { fault } => write!(f, "malformed schema image: {fault}"),
        }
    }
}

impl core::error::Error for SchemaError
{
}

impl fmt::Display for ElementKind
{
    /// Writes the word a refusal names the kind by.
    ///
    /// # Specification
    /// - ensures: writes the kind's lowercase word, two words for an attribute
    ///   type.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unknown-object refusal renders "no object is
    ///   named", distinguishing a swapped kind word.
    /// - witness: `tests::schema::an_unknown_object_is_refused_by_name`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Object => "object",
            | Self::AttributeType => "attribute type",
            | Self::Arrow => "arrow",
            | Self::Attribute => "attribute",
            | Self::Equation => "equation",
        })
    }
}

impl fmt::Display for ImageFault
{
    /// Writes where the image stopped making sense.
    ///
    /// # Specification
    /// - ensures: writes one phrase per fault, distinct for each.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every fault's rendering differs from every other's.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Domain => "the domain is not the schema domain",
            | Self::Truncated => "the image ends inside a field",
            | Self::NotUtf8 => "a name is not UTF-8",
            | Self::IndexingTag => "an indexing byte is neither 0x00 nor 0x01",
            | Self::Ordinal => "an ordinal names no element of its section",
            | Self::Trailing => "bytes follow the last section",
            | Self::NotCanonical => "the image is not the canonical image of what it presents",
        })
    }
}

/// A schema image, borrowed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SchemaImage<'image>(&'image [u8]);

impl<'image> From<&'image [u8]> for SchemaImage<'image>
{
    /// Reads bytes as a candidate image; [`Schema::decode`] decides.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'image [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for SchemaImage<'_>
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// An arrow as a presentation states it, by names.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ArrowSpec
{
    /// The arrow's name.
    name: Name,
    /// The object it leaves.
    source: Name,
    /// The object it reaches.
    target: Name,
    /// Whether its inverse is kept.
    indexing: Indexing,
}

/// An attribute as a presentation states it, by names.
#[derive(Clone, Debug, Eq, PartialEq)]
struct AttributeSpec
{
    /// The attribute's name.
    name: Name,
    /// The object it is a column of.
    object: Name,
    /// Its type.
    ty: Name,
    /// Whether its inverse is kept.
    indexing: Indexing,
}

/// An equation as a presentation states it, by names.
#[derive(Clone, Debug, Eq, PartialEq)]
struct EquationSpec
{
    /// The equation's name.
    name: Name,
    /// The object both paths leave.
    start: Name,
    /// The left path's arrows, first applied first.
    left: Box<[Name]>,
    /// The right path's arrows, first applied first.
    right: Box<[Name]>,
}

/// A schema stated by name, in any order; [`Schema::present`] validates it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Presentation
{
    /// The objects.
    objects: Vec<Name>,
    /// The attribute types.
    attribute_types: Vec<Name>,
    /// The arrows.
    arrows: Vec<ArrowSpec>,
    /// The attributes.
    attributes: Vec<AttributeSpec>,
    /// The equations.
    equations: Vec<EquationSpec>,
}

impl Presentation
{
    /// An empty presentation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            objects: Vec::new(),
            attribute_types: Vec::new(),
            arrows: Vec::new(),
            attributes: Vec::new(),
            equations: Vec::new(),
        }
    }

    /// Adds an object.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn object<N>(
        mut self,
        name: N,
    ) -> Self
    where
        N: Into<Name>,
    {
        self.objects.push(name.into());
        self
    }

    /// Adds an attribute type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn attribute_type<N>(
        mut self,
        name: N,
    ) -> Self
    where
        N: Into<Name>,
    {
        self.attribute_types.push(name.into());
        self
    }

    /// Adds an arrow from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arrow<N, S, T>(
        mut self,
        name: N,
        source: S,
        target: T,
        indexing: Indexing,
    ) -> Self
    where
        N: Into<Name>,
        S: Into<Name>,
        T: Into<Name>,
    {
        self.arrows.push(ArrowSpec {
            name: name.into(),
            source: source.into(),
            target: target.into(),
            indexing,
        });
        self
    }

    /// Adds an attribute of `object` with type `ty`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn attribute<N, O, T>(
        mut self,
        name: N,
        object: O,
        ty: T,
        indexing: Indexing,
    ) -> Self
    where
        N: Into<Name>,
        O: Into<Name>,
        T: Into<Name>,
    {
        self.attributes.push(AttributeSpec {
            name: name.into(),
            object: object.into(),
            ty: ty.into(),
            indexing,
        });
        self
    }

    /// Adds the equation `left = right` between two paths out of `start`,
    /// each listed first arrow first; an empty list is the identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn equation<N, S, L, R, A, B>(
        mut self,
        name: N,
        start: S,
        left: L,
        right: R,
    ) -> Self
    where
        N: Into<Name>,
        S: Into<Name>,
        L: IntoIterator<Item = A>,
        R: IntoIterator<Item = B>,
        A: Into<Name>,
        B: Into<Name>,
    {
        self.equations.push(EquationSpec {
            name: name.into(),
            start: start.into(),
            left: left.into_iter().map(Into::into).collect(),
            right: right.into_iter().map(Into::into).collect(),
        });
        self
    }
}

/// A composable path of arrows out of one object.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Path
{
    /// The object the path leaves.
    start: ObjectId,
    /// The object the path reaches.
    end: ObjectId,
    /// The arrows, first applied first; empty for the identity.
    arrows: Box<[ArrowId]>,
}

impl Path
{
    /// A path from its parts; the caller has checked that it composes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn composed(
        start: ObjectId,
        end: ObjectId,
        arrows: Box<[ArrowId]>,
    ) -> Self
    {
        Self { start, end, arrows }
    }

    /// The object the path leaves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> ObjectId
    {
        self.start
    }

    /// The object the path reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> ObjectId
    {
        self.end
    }

    /// The arrows, first applied first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arrows(&self) -> &[ArrowId]
    {
        &self.arrows
    }
}

/// One arrow of a presented schema.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Arrow
{
    /// The arrow's name.
    name: Name,
    /// The object it leaves.
    source: ObjectId,
    /// The object it reaches.
    target: ObjectId,
    /// Whether its inverse is kept.
    indexing: Indexing,
}

impl Arrow
{
    /// The arrow's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> &Name
    {
        &self.name
    }

    /// The object the arrow leaves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> ObjectId
    {
        self.source
    }

    /// The object the arrow reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> ObjectId
    {
        self.target
    }

    /// Whether the arrow's inverse is kept.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn indexing(&self) -> Indexing
    {
        self.indexing
    }
}

/// One attribute of a presented schema.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Attribute
{
    /// The attribute's name.
    name: Name,
    /// The object it is a column of.
    object: ObjectId,
    /// Its type.
    ty: AttributeTypeId,
    /// Whether its inverse is kept.
    indexing: Indexing,
}

impl Attribute
{
    /// The attribute's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> &Name
    {
        &self.name
    }

    /// The object the attribute is a column of.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn object(&self) -> ObjectId
    {
        self.object
    }

    /// The attribute's type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ty(&self) -> AttributeTypeId
    {
        self.ty
    }

    /// Whether the attribute's inverse is kept.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn indexing(&self) -> Indexing
    {
        self.indexing
    }
}

/// One path equation of a presented schema.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Equation
{
    /// The equation's name.
    name: Name,
    /// The left side.
    left: Path,
    /// The right side.
    right: Path,
}

impl Equation
{
    /// The equation's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> &Name
    {
        &self.name
    }

    /// The left side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> &Path
    {
        &self.left
    }

    /// The right side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> &Path
    {
        &self.right
    }

    /// The side an occurrence names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn side(
        &self,
        side: Side,
    ) -> &Path
    {
        match side {
            | Side::Left => &self.left,
            | Side::Right => &self.right,
        }
    }
}

/// One side of an equation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Side
{
    /// The left side.
    Left,
    /// The right side.
    Right,
}

/// How many arrows of a path precede one occurrence of an arrow in it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathPosition(usize);

impl From<PathPosition> for usize
{
    /// Reads the number of preceding arrows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: PathPosition) -> Self
    {
        position.0
    }
}

/// Where an arrow occurs in the schema's equations: the reverse lookup the
/// equation check starts from when an arrow's value changes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Occurrence
{
    /// The equation.
    pub equation: EquationId,
    /// The side.
    pub side: Side,
    /// The arrows before the occurrence on that side.
    pub position: PathPosition,
}

/// A validated schema with its canonical image and identity.
///
/// # Specification
/// - requires: construction through [`Schema::present`] or [`Schema::decode`].
/// - ensures: every section is sorted strictly by name and names are unique
///   across sections; every arrow, attribute and path names elements of this
///   schema; every equation's sides leave one object and reach one object; the
///   image is the canonical encoding and the identity its BLAKE3.
/// - provides: ordinal lookups and the reverse tables the store reads.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on a schema presented in two orders observes one image and
///   identity; refusals of a duplicate name, a non-composable path and
///   differing endpoints distinguish each validation; the pinned keyed-index
///   identity distinguishes any change to the image layout.
/// - witness: `tests::schema::presentation_order_does_not_change_the_identity`
/// - witness: `tests::schema::a_duplicate_name_is_refused`
/// - witness: `tests::schema::a_path_that_does_not_compose_is_refused_by_name`
/// - witness: `tests::schema::equation_sides_must_meet`
/// - witness: `tests::keyed::the_keyed_schema_identity_is_pinned`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Schema
{
    /// The objects, sorted by name.
    objects: Box<[Name]>,
    /// The attribute types, sorted by name.
    attribute_types: Box<[Name]>,
    /// The arrows, sorted by name.
    arrows: Box<[Arrow]>,
    /// The attributes, sorted by name.
    attributes: Box<[Attribute]>,
    /// The equations, sorted by name.
    equations: Box<[Equation]>,
    /// For each object, the arrows leaving it.
    outgoing: Box<[Box<[ArrowId]>]>,
    /// For each object, the arrows reaching it.
    incoming: Box<[Box<[ArrowId]>]>,
    /// For each object, its attributes.
    fields: Box<[Box<[AttributeId]>]>,
    /// For each object, the equations whose paths leave it.
    rooted: Box<[Box<[EquationId]>]>,
    /// For each arrow, where it occurs in the equations.
    occurrences: Box<[Box<[Occurrence]>]>,
    /// The canonical image.
    image: SchemaImageBuf,
    /// BLAKE3 of the image.
    identity: SchemaIdentity,
}

impl Schema
{
    /// Validates a presentation and fixes its canonical image.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every element of the presentation is in the schema
    ///   under its name, sorted by name, and the identity is BLAKE3 of the
    ///   image; the order of the presentation's statements does not affect the
    ///   result.
    /// - provides: the one constructor from names.
    /// - fails: [`SchemaError::EmptyName`], [`SchemaError::DuplicateName`],
    ///   [`SchemaError::Unknown`] for a name that resolves to no element of the
    ///   kind its position needs, [`SchemaError::NotComposable`],
    ///   [`SchemaError::EndpointsDiffer`] and [`SchemaError::TooLarge`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SchemaError::EmptyName`]: some element's name is empty.
    /// - [`SchemaError::DuplicateName`]: a name is used twice.
    /// - [`SchemaError::Unknown`]: an arrow, attribute or equation names an
    ///   element that is not there.
    /// - [`SchemaError::NotComposable`]: an equation's path takes an arrow out
    ///   of an object it has not reached.
    /// - [`SchemaError::EndpointsDiffer`]: an equation's sides end apart.
    /// - [`SchemaError::TooLarge`]: a section outgrows the image's counts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the refusal witnesses each trigger one validation and
    ///   assert its exact variant and names; the order witness presents the
    ///   same elements reversed and observes the same image.
    /// - witness: `tests::schema::presentation_order_does_not_change_the_identity`
    /// - witness: `tests::schema::a_duplicate_name_is_refused`
    /// - witness: `tests::schema::an_unknown_object_is_refused_by_name`
    /// - witness: `tests::schema::a_path_that_does_not_compose_is_refused_by_name`
    /// - witness: `tests::schema::equation_sides_must_meet`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |schema| schema.identity == identity_of(schema.encode())))]
    pub fn present(presentation: &Presentation) -> Result<Self, SchemaError>
    {
        ensure_names(presentation)?;

        let objects = sorted_names(&presentation.objects);
        let attribute_types = sorted_names(&presentation.attribute_types);
        let object_ordinals = ordinals(&objects);
        let type_ordinals = ordinals(&attribute_types);

        let mut arrows = Vec::with_capacity(presentation.arrows.len());
        for spec in &presentation.arrows {
            let source = resolve(&object_ordinals, ElementKind::Object, &spec.source)?;
            let target = resolve(&object_ordinals, ElementKind::Object, &spec.target)?;
            arrows.push(Arrow {
                name: spec.name.clone(),
                source: ObjectId(source.0),
                target: ObjectId(target.0),
                indexing: spec.indexing,
            });
        }
        arrows.sort_by(|left, right| left.name.cmp(&right.name));
        let arrow_ordinals: BTreeMap<&Name, Ordinal> = arrows
            .iter()
            .enumerate()
            .map(|(ordinal, arrow)| (&arrow.name, Ordinal(ordinal)))
            .collect();

        let mut attributes = Vec::with_capacity(presentation.attributes.len());
        for spec in &presentation.attributes {
            let object = resolve(&object_ordinals, ElementKind::Object, &spec.object)?;
            let ty = resolve(&type_ordinals, ElementKind::AttributeType, &spec.ty)?;
            attributes.push(Attribute {
                name: spec.name.clone(),
                object: ObjectId(object.0),
                ty: AttributeTypeId(ty.0),
                indexing: spec.indexing,
            });
        }
        attributes.sort_by(|left, right| left.name.cmp(&right.name));

        let mut equations = Vec::with_capacity(presentation.equations.len());
        for spec in &presentation.equations {
            let start = resolve(&object_ordinals, ElementKind::Object, &spec.start)?;
            let start = ObjectId(start.0);
            let left = resolve_path(
                &objects,
                &arrows,
                &arrow_ordinals,
                &spec.name,
                start,
                &spec.left,
            )?;
            let right = resolve_path(
                &objects,
                &arrows,
                &arrow_ordinals,
                &spec.name,
                start,
                &spec.right,
            )?;
            if left.end != right.end {
                let left = object_name(&objects, left.end)?;
                let right = object_name(&objects, right.end)?;
                return Err(SchemaError::EndpointsDiffer {
                    equation: spec.name.clone(),
                    left,
                    right,
                });
            }
            equations.push(Equation {
                name: spec.name.clone(),
                left,
                right,
            });
        }
        equations.sort_by(|left, right| left.name.cmp(&right.name));

        Self::assemble(
            objects.into_boxed_slice(),
            attribute_types.into_boxed_slice(),
            arrows.into_boxed_slice(),
            attributes.into_boxed_slice(),
            equations.into_boxed_slice(),
        )
    }

    /// Builds the reverse tables, the image and the identity over sorted,
    /// resolved sections.
    ///
    /// # Specification
    /// - requires: every section is sorted by name and every ordinal is in
    ///   range.
    /// - ensures: each reverse table lists, per object or arrow, exactly the
    ///   elements that name it, in ordinal order; the identity hashes the
    ///   image.
    /// - fails: [`SchemaError::TooLarge`] when a section outgrows a `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::TooLarge`]: a count does not fit the image.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the store's equation check reads the occurrence
    ///   table; the reflexive-loop witness refuses through an occurrence at
    ///   position one and the keyed fixture through one at position zero, so a
    ///   lost or misplaced occurrence leaves a violation unrefused.
    /// - witness: `tests::equations::retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it`
    /// - witness: `tests::keyed::a_naming_whose_task_disagrees_is_refused_by_equation`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |schema| schema.identity == identity_of(schema.encode())))]
    fn assemble(
        objects: Box<[Name]>,
        attribute_types: Box<[Name]>,
        arrows: Box<[Arrow]>,
        attributes: Box<[Attribute]>,
        equations: Box<[Equation]>,
    ) -> Result<Self, SchemaError>
    {
        let mut outgoing: Vec<Vec<ArrowId>> = objects.iter().map(|_object| Vec::new()).collect();
        let mut incoming: Vec<Vec<ArrowId>> = objects.iter().map(|_object| Vec::new()).collect();
        let mut fields: Vec<Vec<AttributeId>> = objects.iter().map(|_object| Vec::new()).collect();
        let mut rooted: Vec<Vec<EquationId>> = objects.iter().map(|_object| Vec::new()).collect();
        let mut occurrences: Vec<Vec<Occurrence>> =
            arrows.iter().map(|_arrow| Vec::new()).collect();

        for (ordinal, arrow) in arrows.iter().enumerate() {
            if let Some(list) = outgoing.get_mut(arrow.source.0) {
                list.push(ArrowId(ordinal));
            }
            if let Some(list) = incoming.get_mut(arrow.target.0) {
                list.push(ArrowId(ordinal));
            }
        }
        for (ordinal, attribute) in attributes.iter().enumerate() {
            if let Some(list) = fields.get_mut(attribute.object.0) {
                list.push(AttributeId(ordinal));
            }
        }
        for (ordinal, equation) in equations.iter().enumerate() {
            if let Some(list) = rooted.get_mut(equation.left.start.0) {
                list.push(EquationId(ordinal));
            }
            for side in [Side::Left, Side::Right] {
                for (position, arrow) in equation.side(side).arrows.iter().enumerate() {
                    if let Some(list) = occurrences.get_mut(arrow.0) {
                        list.push(Occurrence {
                            equation: EquationId(ordinal),
                            side,
                            position: PathPosition(position),
                        });
                    }
                }
            }
        }

        let mut schema = Self {
            objects,
            attribute_types,
            arrows,
            attributes,
            equations,
            outgoing: boxed(outgoing),
            incoming: boxed(incoming),
            fields: boxed(fields),
            rooted: boxed(rooted),
            occurrences: boxed(occurrences),
            image: SchemaImageBuf(Box::default()),
            identity: SchemaIdentity([0_u8; SCHEMA_IDENTITY_LEN]),
        };
        schema.image = schema.write_image()?;
        schema.identity = identity_of(schema.encode());

        Ok(schema)
    }

    /// Writes the canonical image of the sections.
    ///
    /// # Specification
    /// - requires: the sections are sorted and resolved.
    /// - ensures: the bytes are the layout the module documentation states.
    /// - fails: [`SchemaError::TooLarge`] when a count or ordinal outgrows
    ///   `u32`.
    /// - panics: none.
    /// - executable: none — the layout's independent statement is the pinned
    ///   golden, not a second encoder in a predicate.
    ///
    /// # Errors
    /// [`SchemaError::TooLarge`]: a count does not fit the image.
    ///
    /// # Adequacy
    /// - hypothesis: L2 against a hand-built golden image of a two-object
    ///   schema; decoding the golden re-presents the same schema.
    /// - witness: `tests::schema::the_image_is_golden`
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    fn write_image(&self) -> Result<SchemaImageBuf, SchemaError>
    {
        let mut image = ImageWriter(Vec::from(SCHEMA_DOMAIN));

        image.count(Ordinal(self.objects.len()), ElementKind::Object)?;
        for name in &self.objects {
            image.name(name, ElementKind::Object)?;
        }
        image.count(
            Ordinal(self.attribute_types.len()),
            ElementKind::AttributeType,
        )?;
        for name in &self.attribute_types {
            image.name(name, ElementKind::AttributeType)?;
        }
        image.count(Ordinal(self.arrows.len()), ElementKind::Arrow)?;
        for arrow in &self.arrows {
            image.name(&arrow.name, ElementKind::Arrow)?;
            image.count(Ordinal(arrow.source.0), ElementKind::Arrow)?;
            image.count(Ordinal(arrow.target.0), ElementKind::Arrow)?;
            image.indexing(arrow.indexing);
        }
        image.count(Ordinal(self.attributes.len()), ElementKind::Attribute)?;
        for attribute in &self.attributes {
            image.name(&attribute.name, ElementKind::Attribute)?;
            image.count(Ordinal(attribute.object.0), ElementKind::Attribute)?;
            image.count(Ordinal(attribute.ty.0), ElementKind::Attribute)?;
            image.indexing(attribute.indexing);
        }
        image.count(Ordinal(self.equations.len()), ElementKind::Equation)?;
        for equation in &self.equations {
            image.name(&equation.name, ElementKind::Equation)?;
            image.count(Ordinal(equation.left.start.0), ElementKind::Equation)?;
            for side in [&equation.left, &equation.right] {
                image.count(Ordinal(side.arrows.len()), ElementKind::Equation)?;
                for arrow in &side.arrows {
                    image.count(Ordinal(arrow.0), ElementKind::Equation)?;
                }
            }
        }

        Ok(SchemaImageBuf(image.0.into_boxed_slice()))
    }

    /// Reads a schema back from its canonical image.
    ///
    /// # Specification
    /// - requires: nothing; any bytes are admitted as input.
    /// - ensures: on success the schema's image equals `image` byte for byte.
    /// - provides: the inverse of [`Schema::encode`] on its range.
    /// - fails: [`SchemaError::Image`] naming where the image stopped making
    ///   sense, including [`ImageFault::NotCanonical`] for bytes that present a
    ///   schema whose image differs; and every refusal [`Schema::present`]
    ///   makes of the presentation the image states.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SchemaError::Image`]: the bytes are not a canonical image.
    /// - Any [`Schema::present`] refusal of the stated presentation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a golden round-trips; a wrong domain, every proper
    ///   prefix, a trailing byte, an out-of-range ordinal and a reordered
    ///   section each receive their named fault.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |schema| schema.encode() == image))]
    pub fn decode(image: SchemaImage<'_>) -> Result<Self, SchemaError>
    {
        let mut cursor = Cursor { rest: image.0 };
        cursor.expect_domain()?;

        let objects = cursor.names()?;
        let attribute_types = cursor.names()?;

        let mut presentation = Presentation::new();
        presentation.objects.clone_from(&objects);
        presentation.attribute_types.clone_from(&attribute_types);

        let arrow_count = cursor.count()?;
        for _arrow in 0_usize .. arrow_count.0 {
            let name = cursor.name()?;
            let source = cursor.count()?;
            let source = pick(&objects, source)?;
            let target = cursor.count()?;
            let target = pick(&objects, target)?;
            let indexing = cursor.indexing()?;
            presentation.arrows.push(ArrowSpec {
                name,
                source,
                target,
                indexing,
            });
        }

        let attribute_count = cursor.count()?;
        for _attribute in 0_usize .. attribute_count.0 {
            let name = cursor.name()?;
            let object = cursor.count()?;
            let object = pick(&objects, object)?;
            let ty = cursor.count()?;
            let ty = pick(&attribute_types, ty)?;
            let indexing = cursor.indexing()?;
            presentation.attributes.push(AttributeSpec {
                name,
                object,
                ty,
                indexing,
            });
        }

        let arrow_names: Vec<Name> = presentation
            .arrows
            .iter()
            .map(|arrow| arrow.name.clone())
            .collect();
        let equation_count = cursor.count()?;
        for _equation in 0_usize .. equation_count.0 {
            let name = cursor.name()?;
            let start = cursor.count()?;
            let start = pick(&objects, start)?;
            let left = cursor.path(&arrow_names)?;
            let right = cursor.path(&arrow_names)?;
            presentation.equations.push(EquationSpec {
                name,
                start,
                left,
                right,
            });
        }

        if !cursor.rest.is_empty() {
            return Err(SchemaError::Image {
                fault: ImageFault::Trailing,
            });
        }

        let schema = Self::present(&presentation)?;
        if schema.encode() != image {
            return Err(SchemaError::Image {
                fault: ImageFault::NotCanonical,
            });
        }

        Ok(schema)
    }

    /// The canonical image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn encode(&self) -> SchemaImage<'_>
    {
        SchemaImage(&self.image.0)
    }

    /// BLAKE3 of the canonical image: the identity a store manifest commits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn identity(&self) -> SchemaIdentity
    {
        self.identity
    }

    /// The objects, in ordinal order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn objects(&self) -> impl ExactSizeIterator<Item = ObjectId> + use<'_>
    {
        (0_usize .. self.objects.len()).map(ObjectId)
    }

    /// The arrows, in ordinal order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn arrows(&self) -> impl ExactSizeIterator<Item = ArrowId> + use<'_>
    {
        (0_usize .. self.arrows.len()).map(ArrowId)
    }

    /// The attributes, in ordinal order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn attributes(&self) -> impl ExactSizeIterator<Item = AttributeId> + use<'_>
    {
        (0_usize .. self.attributes.len()).map(AttributeId)
    }

    /// The equations, in ordinal order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn equations(&self) -> impl ExactSizeIterator<Item = EquationId> + use<'_>
    {
        (0_usize .. self.equations.len()).map(EquationId)
    }

    /// Looks an object up by name.
    ///
    /// # Specification
    /// - ensures: on success the object at the returned ordinal has the name.
    /// - fails: [`SchemaError::Unknown`] with [`ElementKind::Object`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Unknown`]: no object has the name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every fixture resolves its objects by name, and an
    ///   arrow's name looked up as an object is refused.
    /// - witness: `tests::schema::a_lookup_of_the_wrong_kind_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| self.objects.get(id.0).is_some()))]
    pub fn object<N>(
        &self,
        name: N,
    ) -> Result<ObjectId, SchemaError>
    where
        N: Into<Name>,
    {
        let name = name.into();
        self.objects
            .binary_search(&name)
            .map(ObjectId)
            .map_err(|_position| SchemaError::Unknown {
                kind: ElementKind::Object,
                name,
            })
    }

    /// Looks an attribute type up by name.
    ///
    /// # Specification
    /// - ensures: on success the type at the returned ordinal has the name.
    /// - fails: [`SchemaError::Unknown`] with [`ElementKind::AttributeType`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Unknown`]: no attribute type has the name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the schema-map witness maps attributes by their
    ///   type's name, and a map onto a different type is refused.
    /// - witness: `tests::migrate::a_map_onto_another_attribute_type_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| self.attribute_types.get(id.0).is_some()))]
    pub fn attribute_type<N>(
        &self,
        name: N,
    ) -> Result<AttributeTypeId, SchemaError>
    where
        N: Into<Name>,
    {
        let name = name.into();
        self.attribute_types
            .binary_search(&name)
            .map(AttributeTypeId)
            .map_err(|_position| SchemaError::Unknown {
                kind: ElementKind::AttributeType,
                name,
            })
    }

    /// Looks an arrow up by name.
    ///
    /// # Specification
    /// - ensures: on success the arrow at the returned ordinal has the name.
    /// - fails: [`SchemaError::Unknown`] with [`ElementKind::Arrow`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Unknown`]: no arrow has the name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every fixture resolves its arrows by name, and an
    ///   object's name looked up as an arrow is refused.
    /// - witness: `tests::schema::a_lookup_of_the_wrong_kind_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| self.arrows.get(id.0).is_some()))]
    pub fn arrow<N>(
        &self,
        name: N,
    ) -> Result<ArrowId, SchemaError>
    where
        N: Into<Name>,
    {
        let name = name.into();
        self.arrows
            .binary_search_by(|arrow| arrow.name.cmp(&name))
            .map(ArrowId)
            .map_err(|_position| SchemaError::Unknown {
                kind: ElementKind::Arrow,
                name,
            })
    }

    /// Looks an attribute up by name.
    ///
    /// # Specification
    /// - ensures: on success the attribute at the returned ordinal has the
    ///   name.
    /// - fails: [`SchemaError::Unknown`] with [`ElementKind::Attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Unknown`]: no attribute has the name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the keyed fixture resolves every attribute by name
    ///   and reads each back; an unknown attribute name is refused.
    /// - witness: `tests::schema::a_lookup_of_the_wrong_kind_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| self.attributes.get(id.0).is_some()))]
    pub fn attribute<N>(
        &self,
        name: N,
    ) -> Result<AttributeId, SchemaError>
    where
        N: Into<Name>,
    {
        let name = name.into();
        self.attributes
            .binary_search_by(|attribute| attribute.name.cmp(&name))
            .map(AttributeId)
            .map_err(|_position| SchemaError::Unknown {
                kind: ElementKind::Attribute,
                name,
            })
    }

    /// Looks an equation up by name.
    ///
    /// # Specification
    /// - ensures: on success the equation at the returned ordinal has the name.
    /// - fails: [`SchemaError::Unknown`] with [`ElementKind::Equation`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Unknown`]: no equation has the name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the keyed fixture resolves its equation by name and
    ///   reads its sides; an arrow name looked up as an equation is refused.
    /// - witness: `tests::schema::a_lookup_of_the_wrong_kind_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| self.equations.get(id.0).is_some()))]
    pub fn equation<N>(
        &self,
        name: N,
    ) -> Result<EquationId, SchemaError>
    where
        N: Into<Name>,
    {
        let name = name.into();
        self.equations
            .binary_search_by(|equation| equation.name.cmp(&name))
            .map(EquationId)
            .map_err(|_position| SchemaError::Unknown {
                kind: ElementKind::Equation,
                name,
            })
    }

    /// The name of an object.
    ///
    /// # Specification
    /// - ensures: on success, the name at the object's ordinal.
    /// - fails: [`SchemaError::UnknownOrdinal`] out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`]: the ordinal is out of range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusals name their object through this lookup; the
    ///   defect witness asserts the exact object name in its refusal.
    /// - witness: `tests::defect::deleting_the_middle_vertex_refuses_by_name`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(object) < self.objects.len()))]
    pub fn object_name(
        &self,
        object: ObjectId,
    ) -> Result<&Name, SchemaError>
    {
        self.objects
            .get(object.0)
            .ok_or(SchemaError::UnknownOrdinal {
                kind: ElementKind::Object,
                ordinal: Ordinal(object.0),
            })
    }

    /// The name of an attribute type.
    ///
    /// # Specification
    /// - ensures: on success, the name at the type's ordinal.
    /// - fails: [`SchemaError::UnknownOrdinal`] out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`]: the ordinal is out of range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a schema map compares attribute types by name through
    ///   this lookup; the map witness refuses a type change.
    /// - witness: `tests::migrate::a_map_onto_another_attribute_type_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(ty) < self.attribute_types.len()))]
    pub fn attribute_type_name(
        &self,
        ty: AttributeTypeId,
    ) -> Result<&Name, SchemaError>
    {
        self.attribute_types
            .get(ty.0)
            .ok_or(SchemaError::UnknownOrdinal {
                kind: ElementKind::AttributeType,
                ordinal: Ordinal(ty.0),
            })
    }

    /// One arrow.
    ///
    /// # Specification
    /// - ensures: on success, the arrow at the ordinal.
    /// - fails: [`SchemaError::UnknownOrdinal`] out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`]: the ordinal is out of range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ordinal past the last arrow is refused by kind and
    ///   ordinal.
    /// - witness: `tests::schema::an_ordinal_out_of_range_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(arrow) < self.arrows.len()))]
    pub fn arrow_at(
        &self,
        arrow: ArrowId,
    ) -> Result<&Arrow, SchemaError>
    {
        self.arrows.get(arrow.0).ok_or(SchemaError::UnknownOrdinal {
            kind: ElementKind::Arrow,
            ordinal: Ordinal(arrow.0),
        })
    }

    /// One attribute.
    ///
    /// # Specification
    /// - ensures: on success, the attribute at the ordinal.
    /// - fails: [`SchemaError::UnknownOrdinal`] out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`]: the ordinal is out of range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ordinal past the last attribute is refused by kind
    ///   and ordinal.
    /// - witness: `tests::schema::an_ordinal_out_of_range_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(attribute) < self.attributes.len()))]
    pub fn attribute_at(
        &self,
        attribute: AttributeId,
    ) -> Result<&Attribute, SchemaError>
    {
        self.attributes
            .get(attribute.0)
            .ok_or(SchemaError::UnknownOrdinal {
                kind: ElementKind::Attribute,
                ordinal: Ordinal(attribute.0),
            })
    }

    /// One equation.
    ///
    /// # Specification
    /// - ensures: on success, the equation at the ordinal.
    /// - fails: [`SchemaError::UnknownOrdinal`] out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::UnknownOrdinal`]: the ordinal is out of range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ordinal past the last equation is refused by kind
    ///   and ordinal.
    /// - witness: `tests::schema::an_ordinal_out_of_range_is_refused`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(equation) < self.equations.len()))]
    pub fn equation_at(
        &self,
        equation: EquationId,
    ) -> Result<&Equation, SchemaError>
    {
        self.equations
            .get(equation.0)
            .ok_or(SchemaError::UnknownOrdinal {
                kind: ElementKind::Equation,
                ordinal: Ordinal(equation.0),
            })
    }

    /// The arrows leaving an object, in ordinal order; empty out of range.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn outgoing(
        &self,
        object: ObjectId,
    ) -> &[ArrowId]
    {
        self.outgoing.get(object.0).map_or(&[], |list| list)
    }

    /// The arrows reaching an object, in ordinal order; empty out of range.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn incoming(
        &self,
        object: ObjectId,
    ) -> &[ArrowId]
    {
        self.incoming.get(object.0).map_or(&[], |list| list)
    }

    /// The attributes of an object, in ordinal order; empty out of range.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn fields(
        &self,
        object: ObjectId,
    ) -> &[AttributeId]
    {
        self.fields.get(object.0).map_or(&[], |list| list)
    }

    /// The equations whose paths leave an object; empty out of range.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rooted(
        &self,
        object: ObjectId,
    ) -> &[EquationId]
    {
        self.rooted.get(object.0).map_or(&[], |list| list)
    }

    /// Where an arrow occurs in the equations; empty out of range.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn occurrences(
        &self,
        arrow: ArrowId,
    ) -> &[Occurrence]
    {
        self.occurrences.get(arrow.0).map_or(&[], |list| list)
    }

    /// The number of objects.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn object_count(&self) -> ElementCount
    {
        ElementCount(self.objects.len())
    }
}

/// How many elements a schema section holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ElementCount(usize);

impl From<ElementCount> for usize
{
    /// Reads the count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ElementCount) -> Self
    {
        count.0
    }
}

/// BLAKE3 of a schema image.
///
/// # Specification
/// trivial.
#[inline]
fn identity_of(image: SchemaImage<'_>) -> SchemaIdentity
{
    SchemaIdentity(*blake3::hash(image.0).as_bytes())
}

/// An owned canonical schema image.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct SchemaImageBuf(Box<[u8]>);

/// An image being written.
#[repr(transparent)]
struct ImageWriter(Vec<u8>);

impl ImageWriter
{
    /// Appends a count or ordinal as `u32le`.
    ///
    /// # Specification
    /// - ensures: on success four little-endian bytes of the value are
    ///   appended.
    /// - fails: [`SchemaError::TooLarge`] with `kind` above `u32::MAX`,
    ///   appending nothing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::TooLarge`]: the value does not fit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden image pins every count's width and byte
    ///   order.
    /// - witness: `tests::schema::the_image_is_golden`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == u32::try_from(value.0).is_ok())]
    fn count(
        &mut self,
        value: Ordinal,
        kind: ElementKind,
    ) -> Result<(), SchemaError>
    {
        let value = u32::try_from(value.0).map_err(|_overflow| SchemaError::TooLarge { kind })?;
        self.0.extend_from_slice(&value.to_le_bytes());
        Ok(())
    }

    /// Appends a length-prefixed name.
    ///
    /// # Specification
    /// - ensures: on success a `u32le` byte length and the name's bytes are
    ///   appended.
    /// - fails: [`SchemaError::TooLarge`] with `kind` for a name longer than
    ///   `u32::MAX` bytes.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::TooLarge`]: the name does not fit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden image pins every name's prefix and bytes.
    /// - witness: `tests::schema::the_image_is_golden`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == u32::try_from(name.0.len()).is_ok())]
    fn name(
        &mut self,
        name: &Name,
        kind: ElementKind,
    ) -> Result<(), SchemaError>
    {
        self.count(Ordinal(name.0.len()), kind)?;
        self.0.extend_from_slice(name.0.as_bytes());
        Ok(())
    }

    /// Appends an indexing byte: `0x00` unindexed, `0x01` indexed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn indexing(
        &mut self,
        indexing: Indexing,
    )
    {
        self.0.push(match indexing {
            | Indexing::Unindexed => 0x00_u8,
            | Indexing::Indexed => 0x01_u8,
        });
    }
}

/// Refuses an empty name and a name used twice anywhere in a presentation.
///
/// # Specification
/// - ensures: success exactly when every name is nonempty and all names are
///   distinct.
/// - fails: [`SchemaError::EmptyName`] first, by statement order, then
///   [`SchemaError::DuplicateName`] for the first repeat.
/// - panics: none.
/// - executable: none — the predicate would re-collect every name, the work the
///   body does.
///
/// # Errors
/// [`SchemaError::EmptyName`] or [`SchemaError::DuplicateName`].
///
/// # Adequacy
/// - hypothesis: L3 — an arrow named as an object is refused with that name; an
///   empty object name is refused.
/// - witness: `tests::schema::a_duplicate_name_is_refused`
#[inline]
fn ensure_names(presentation: &Presentation) -> Result<(), SchemaError>
{
    let names = presentation
        .objects
        .iter()
        .chain(&presentation.attribute_types)
        .chain(presentation.arrows.iter().map(|arrow| &arrow.name))
        .chain(
            presentation
                .attributes
                .iter()
                .map(|attribute| &attribute.name),
        )
        .chain(presentation.equations.iter().map(|equation| &equation.name));

    let mut seen = BTreeSet::new();
    for name in names {
        if name.0.is_empty() {
            return Err(SchemaError::EmptyName);
        }
        if !seen.insert(name) {
            return Err(SchemaError::DuplicateName { name: name.clone() });
        }
    }

    Ok(())
}

/// The names, sorted.
///
/// # Specification
/// trivial.
#[inline]
fn sorted_names(names: &[Name]) -> Vec<Name>
{
    let mut sorted = names.to_vec();
    sorted.sort();
    sorted
}

/// Each sorted name's ordinal.
///
/// # Specification
/// trivial.
#[inline]
fn ordinals(names: &[Name]) -> BTreeMap<&Name, Ordinal>
{
    names
        .iter()
        .enumerate()
        .map(|(ordinal, name)| (name, Ordinal(ordinal)))
        .collect()
}

/// Resolves a name in a section.
///
/// # Specification
/// - ensures: on success the ordinal the section maps the name to.
/// - fails: [`SchemaError::Unknown`] with `kind` and the name.
/// - panics: none.
///
/// # Errors
/// [`SchemaError::Unknown`]: the section has no such name.
///
/// # Adequacy
/// - hypothesis: L3 — an arrow into an undeclared object is refused with the
///   object kind and its name.
/// - witness: `tests::schema::an_unknown_object_is_refused_by_name`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == ordinals.contains_key(name))]
fn resolve(
    ordinals: &BTreeMap<&Name, Ordinal>,
    kind: ElementKind,
    name: &Name,
) -> Result<Ordinal, SchemaError>
{
    ordinals
        .get(name)
        .copied()
        .ok_or_else(|| SchemaError::Unknown {
            kind,
            name: name.clone(),
        })
}

/// The name at an object ordinal.
///
/// # Specification
/// - ensures: on success the name at the ordinal.
/// - fails: [`SchemaError::UnknownOrdinal`] out of range.
/// - panics: none.
///
/// # Errors
/// [`SchemaError::UnknownOrdinal`]: the ordinal is out of range.
///
/// # Adequacy
/// - hypothesis: L3 — the endpoint refusal names both end objects through this
///   lookup.
/// - witness: `tests::schema::equation_sides_must_meet`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == (object.0 < objects.len()))]
fn object_name(
    objects: &[Name],
    object: ObjectId,
) -> Result<Name, SchemaError>
{
    objects
        .get(object.0)
        .cloned()
        .ok_or(SchemaError::UnknownOrdinal {
            kind: ElementKind::Object,
            ordinal: Ordinal(object.0),
        })
}

/// Resolves and composes one side of an equation.
///
/// # Specification
/// - requires: `arrows` is sorted and `arrow_ordinals` maps its names.
/// - ensures: on success the path leaves `start`, each arrow leaves the object
///   the path has reached, and the end is the last arrow's target or `start`.
/// - fails: [`SchemaError::Unknown`] for an arrow name, and
///   [`SchemaError::NotComposable`] naming the equation, the arrow and the
///   object reached.
/// - panics: none.
///
/// # Errors
/// [`SchemaError::Unknown`] or [`SchemaError::NotComposable`].
///
/// # Adequacy
/// - hypothesis: L3 — a path taking `tgt` out of the vertex object is refused
///   with the equation, arrow and object names; identity paths resolve in the
///   reflexive-loop schema.
/// - witness: `tests::schema::a_path_that_does_not_compose_is_refused_by_name`
/// - witness: `tests::equations::a_loop_that_leaves_its_vertex_is_refused_by_equation`
#[inline]
#[spec(ensures: |ret| ret.as_ref().map_or(true, |path| path.start == start && path.arrows.len() == names.len()))]
fn resolve_path(
    objects: &[Name],
    arrows: &[Arrow],
    arrow_ordinals: &BTreeMap<&Name, Ordinal>,
    equation: &Name,
    start: ObjectId,
    names: &[Name],
) -> Result<Path, SchemaError>
{
    let mut at = start;
    let mut path = Vec::with_capacity(names.len());

    for name in names {
        let ordinal = resolve(arrow_ordinals, ElementKind::Arrow, name)?;
        let arrow = arrows.get(ordinal.0).ok_or(SchemaError::UnknownOrdinal {
            kind: ElementKind::Arrow,
            ordinal,
        })?;
        if arrow.source != at {
            let at = object_name(objects, at)?;
            return Err(SchemaError::NotComposable {
                equation: equation.clone(),
                arrow: name.clone(),
                at,
            });
        }
        at = arrow.target;
        path.push(ArrowId(ordinal.0));
    }

    Ok(Path {
        start,
        end: at,
        arrows: path.into_boxed_slice(),
    })
}

/// Boxes each inner list and the outer one.
///
/// # Specification
/// trivial.
#[inline]
fn boxed<T>(lists: Vec<Vec<T>>) -> Box<[Box<[T]>]>
{
    lists.into_iter().map(Vec::into_boxed_slice).collect()
}

/// The name at an ordinal of a decoded section.
///
/// # Specification
/// - ensures: on success the name at the ordinal.
/// - fails: [`SchemaError::Image`] with [`ImageFault::Ordinal`] out of range.
/// - panics: none.
///
/// # Errors
/// [`SchemaError::Image`]: the ordinal is out of range.
///
/// # Adequacy
/// - hypothesis: L3 — an image whose arrow names object ordinal two of two is
///   refused with the ordinal fault.
/// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == (ordinal.0 < names.len()))]
fn pick(
    names: &[Name],
    ordinal: Ordinal,
) -> Result<Name, SchemaError>
{
    names.get(ordinal.0).cloned().ok_or(SchemaError::Image {
        fault: ImageFault::Ordinal,
    })
}

/// A read position in a schema image.
#[repr(transparent)]
struct Cursor<'image>
{
    /// The bytes not yet read.
    rest: &'image [u8],
}

impl Cursor<'_>
{
    /// Consumes the domain.
    ///
    /// # Specification
    /// - ensures: on success the domain is consumed.
    /// - fails: [`ImageFault::Domain`] when the image does not open with it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Image`] with [`ImageFault::Domain`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an image whose domain's last byte is changed is
    ///   refused with the domain fault.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    #[spec(
        captures: before = self.rest.len(),
        ensures: |ret| ret.is_err() || before.checked_sub(self.rest.len()) == Some(SCHEMA_DOMAIN.len()),
    )]
    fn expect_domain(&mut self) -> Result<(), SchemaError>
    {
        match self.rest.strip_prefix(SCHEMA_DOMAIN) {
            | Some(rest) => {
                self.rest = rest;
                Ok(())
            },
            | None => Err(SchemaError::Image {
                fault: ImageFault::Domain,
            }),
        }
    }

    /// Consumes a `u32le` count or ordinal.
    ///
    /// # Specification
    /// - ensures: on success the little-endian value of four consumed bytes.
    /// - fails: [`ImageFault::Truncated`] when fewer remain, and
    ///   [`ImageFault::Ordinal`] on a target whose `usize` cannot hold it.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the golden round
    ///   trip is its independent observation.
    ///
    /// # Errors
    /// [`SchemaError::Image`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden decodes to the schema it was written from,
    ///   so a byte-order or width fault changes some ordinal; every proper
    ///   prefix is refused as truncated.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    fn count(&mut self) -> Result<Ordinal, SchemaError>
    {
        let (bytes, rest) = self
            .rest
            .split_first_chunk::<4>()
            .ok_or(SchemaError::Image {
                fault: ImageFault::Truncated,
            })?;
        self.rest = rest;
        usize::try_from(u32::from_le_bytes(*bytes))
            .map(Ordinal)
            .map_err(|_overflow| SchemaError::Image {
                fault: ImageFault::Ordinal,
            })
    }

    /// Consumes a length-prefixed name.
    ///
    /// # Specification
    /// - ensures: on success the name the prefix and bytes state.
    /// - fails: [`ImageFault::Truncated`] or [`ImageFault::NotUtf8`].
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the golden round
    ///   trip is its independent observation.
    ///
    /// # Errors
    /// [`SchemaError::Image`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name byte replaced by `0xff` is refused as not
    ///   UTF-8; the golden round-trips every name.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    fn name(&mut self) -> Result<Name, SchemaError>
    {
        let length = self.count()?;
        let (bytes, rest) = self
            .rest
            .split_at_checked(length.0)
            .ok_or(SchemaError::Image {
                fault: ImageFault::Truncated,
            })?;
        self.rest = rest;
        let text = core::str::from_utf8(bytes).map_err(|_invalid| SchemaError::Image {
            fault: ImageFault::NotUtf8,
        })?;
        Ok(Name::from(text))
    }

    /// Consumes a counted section of names.
    ///
    /// # Specification
    /// - ensures: on success the names in image order.
    /// - fails: as [`Cursor::count`] and [`Cursor::name`].
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the golden round
    ///   trip is its independent observation.
    ///
    /// # Errors
    /// [`SchemaError::Image`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden's object and type sections decode to their
    ///   names in order.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    fn names(&mut self) -> Result<Vec<Name>, SchemaError>
    {
        let count = self.count()?;
        let mut names = Vec::new();
        for _name in 0_usize .. count.0 {
            let name = self.name()?;
            names.push(name);
        }
        Ok(names)
    }

    /// Consumes an indexing byte.
    ///
    /// # Specification
    /// - ensures: on success `0x00` reads as unindexed and `0x01` as indexed.
    /// - fails: [`ImageFault::Truncated`], or [`ImageFault::IndexingTag`] for
    ///   any other byte.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SchemaError::Image`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an indexing byte of `0x02` is refused with the tag
    ///   fault; the golden carries both values.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    #[spec(
        captures: first = self.rest.first().copied(),
        ensures: |ret| match ret {
            Ok(Indexing::Unindexed) => first == Some(0x00_u8),
            Ok(Indexing::Indexed) => first == Some(0x01_u8),
            Err(_) => !matches!(first, Some(0x00_u8 | 0x01_u8)),
        },
    )]
    fn indexing(&mut self) -> Result<Indexing, SchemaError>
    {
        let (tag, rest) = self.rest.split_first().ok_or(SchemaError::Image {
            fault: ImageFault::Truncated,
        })?;
        let indexing = match *tag {
            | 0x00_u8 => Indexing::Unindexed,
            | 0x01_u8 => Indexing::Indexed,
            | _ => {
                return Err(SchemaError::Image {
                    fault: ImageFault::IndexingTag,
                });
            },
        };
        self.rest = rest;
        Ok(indexing)
    }

    /// Consumes a path, resolving its arrow ordinals to names.
    ///
    /// # Specification
    /// - ensures: on success the arrow names in path order.
    /// - fails: as [`Cursor::count`], and [`ImageFault::Ordinal`] for an arrow
    ///   ordinal out of range.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the golden round
    ///   trip is its independent observation.
    ///
    /// # Errors
    /// [`SchemaError::Image`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the golden's equation decodes to its two paths.
    /// - witness: `tests::schema::an_image_round_trips_and_malformed_ones_are_refused`
    #[inline]
    fn path(
        &mut self,
        arrows: &[Name],
    ) -> Result<Box<[Name]>, SchemaError>
    {
        let length = self.count()?;
        let mut path = Vec::new();
        for _arrow in 0_usize .. length.0 {
            let ordinal = self.count()?;
            let arrow = pick(arrows, ordinal)?;
            path.push(arrow);
        }
        Ok(path.into_boxed_slice())
    }
}
