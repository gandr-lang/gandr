//! Flat dependency-ordered program images and their little-endian wire.

use anodized::spec;

/// An address in the image arena.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct NodeIndex(u32);
impl From<u32> for NodeIndex
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}
impl From<NodeIndex> for u32
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NodeIndex) -> Self
    {
        value.0
    }
}

/// A de Bruijn index counted from the innermost binder.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BinderIndex(u32);
impl From<u32> for BinderIndex
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}
impl From<BinderIndex> for u32
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: BinderIndex) -> Self
    {
        value.0
    }
}

/// A signed integer payload in the image.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Literal(i64);
impl From<i64> for Literal
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i64) -> Self
    {
        Self(value)
    }
}
impl From<Literal> for i64
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Literal) -> Self
    {
        value.0
    }
}

/// The number of image nodes.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct NodeCount(usize);
impl From<usize> for NodeCount
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<NodeCount> for usize
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NodeCount) -> Self
    {
        value.0
    }
}

/// A static count of accounted operations.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct WorkCount(i64);
impl From<i64> for WorkCount
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i64) -> Self
    {
        Self(value)
    }
}
impl From<WorkCount> for i64
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WorkCount) -> Self
    {
        value.0
    }
}

/// One discriminant byte in the image wire.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct WireByte(u8);
impl From<u8> for WireByte
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u8) -> Self
    {
        Self(value)
    }
}
impl From<WireByte> for u8
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WireByte) -> Self
    {
        value.0
    }
}

/// The number of fields a constructor takes.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct CtorArity(usize);
impl From<usize> for CtorArity
{
    /// Wrap the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<CtorArity> for usize
{
    /// Expose the payload at the numeric boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CtorArity) -> Self
    {
        value.0
    }
}

/// Positive-core operation tags, independent of Rust declaration order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NodeKind
{
    /// Integer literal.
    Lit,
    /// Bound variable.
    Var,
    /// Positive constructor.
    Ctor,
    /// Accounted duplication.
    Dup,
    /// Accounted discard.
    Drop,
    /// Sequencing binder.
    Bind,
    /// Sum elimination.
    Case,
    /// Terminal cut.
    Cut,
}
impl NodeKind
{
    /// The version-one operation discriminant.
    ///
    /// # Specification
    /// - ensures: the ordered vocabulary Lit, Var, Ctor, Dup, Drop, Bind, Case,
    ///   Cut maps to bytes zero through seven.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 pinned wire bytes distinguish tag substitutions.
    /// - witness: `tests::contract::the_wire_numbering_matches_this_crates_mirror`
    #[spec(ensures: |ret| ret.0 < 8)]
    #[must_use]
    #[inline]
    pub const fn wire_byte(self) -> WireByte
    {
        WireByte(match self {
            | Self::Lit => 0,
            | Self::Var => 1,
            | Self::Ctor => 2,
            | Self::Dup => 3,
            | Self::Drop => 4,
            | Self::Bind => 5,
            | Self::Case => 6,
            | Self::Cut => 7,
        })
    }
}
/// The positive constructor vocabulary.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CtorTag
{
    /// Unit, with no fields.
    #[default]
    Unit,
    /// Pair, with two ordered fields.
    Pair,
    /// Left injection, with one field.
    Inl,
    /// Right injection, with one field.
    Inr,
}
impl CtorTag
{
    /// The version-one constructor discriminant.
    ///
    /// # Specification
    /// - ensures: Unit, Pair, Inl and Inr map to zero, one, two and three.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 pinned wire bytes distinguish tag substitutions.
    /// - witness: `tests::contract::the_wire_numbering_matches_this_crates_mirror`
    #[spec(ensures: |ret| ret.0 < 4)]
    #[must_use]
    #[inline]
    pub const fn wire_byte(self) -> WireByte
    {
        WireByte(match self {
            | Self::Unit => 0,
            | Self::Pair => 1,
            | Self::Inl => 2,
            | Self::Inr => 3,
        })
    }
    /// The constructor's field count.
    ///
    /// # Specification
    /// - ensures: Unit has no fields, Pair has two, each injection has one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 enumerates every constructor arity.
    /// - witness: `tests::contract::the_constructor_arities_match_this_crates_mirror`
    #[spec(ensures: |ret| ret.0 <= 2)]
    #[must_use]
    #[inline]
    pub const fn arity(self) -> CtorArity
    {
        CtorArity(match self {
            | Self::Unit => 0,
            | Self::Pair => 2,
            | Self::Inl | Self::Inr => 1,
        })
    }
}
/// A wire record; fields unused by the kind are zero in lowered images.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node
{
    /// Operation kind.
    pub kind: NodeKind,
    /// Constructor tag.
    pub tag: CtorTag,
    /// Variable distance.
    pub binder: BinderIndex,
    /// Integer payload.
    pub literal: Literal,
    /// Operands in semantic order.
    pub operands: Vec<NodeIndex>,
}
/// Version one's inclusive node ceiling.
pub const MAX_IMAGE_NODES: usize = 4096;
/// Image wire version.
pub const IMAGE_WIRE_VERSION: u8 = 1;
/// A bounded flat arena whose last node is the entry.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Image
{
    /// Records in dependency order.
    nodes: Vec<Node>,
}
/// Static operation counts; with a case these are upper bounds, not a run
/// ledger.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct AccountedWork
{
    /// Duplication nodes.
    pub duplications: WorkCount,
    /// Discard nodes.
    pub discards: WorkCount,
}
/// Whether an image contains a case.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DispatchPresence
{
    /// Every node belongs to the straight-line path.
    Absent,
    /// A case chooses between arms.
    Present,
}
/// A size or address the wire cannot encode faithfully.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImageError
{
    /// The node ceiling would be exceeded.
    TooManyNodes,
    /// The operand count would exceed one byte.
    TooManyOperands,
    /// An operand does not precede its node.
    ForwardOperand(NodeIndex),
}
impl core::fmt::Display for ImageError
{
    /// Render the precise refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::TooManyNodes => f.write_str("image exceeds 4096 nodes"),
            | Self::TooManyOperands => f.write_str("node exceeds 255 operands"),
            | Self::ForwardOperand(index) => {
                write!(f, "operand {} does not precede its node", index.0)
            },
        }
    }
}
impl core::error::Error for ImageError
{
}
/// Encoded image bytes, ready for a host to read.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct ImageBytes(Vec<u8>);
impl AsRef<[u8]> for ImageBytes
{
    /// Borrow the encoded wire.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}
impl Image
{
    /// Create an empty image.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new() -> Self
    {
        Self { nodes: Vec::new() }
    }
    /// Borrow records in dependency order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn nodes(&self) -> &[Node]
    {
        &self.nodes
    }
    /// Count records.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn len(&self) -> NodeCount
    {
        NodeCount(self.nodes.len())
    }
    /// Append one faithfully encodable node, preserving the arena on refusal.
    ///
    /// # Specification
    /// - ensures: success returns the appended node's position; refusal leaves
    ///   the arena unchanged. Operands refer strictly backwards.
    /// - fails: node ceiling, operand-byte overflow, or a forward operand.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the matching `ImageError` variant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 ceiling, operand-count and reference boundaries
    ///   separate rejection from silent truncation and changed refusal state.
    /// - witness: `tests::image::the_arena_refuses_a_node_past_the_declared_bound`
    /// - witness: `tests::image::unencodable_operands_preserve_the_arena`
    #[spec(captures: count = self.nodes.len(), ensures: |ret| self.nodes.len() == count.saturating_add(usize::from(ret.is_ok())))]
    #[inline]
    pub fn push(
        &mut self,
        node: Node,
    ) -> Result<NodeIndex, ImageError>
    {
        if self.nodes.len() >= MAX_IMAGE_NODES {
            return Err(ImageError::TooManyNodes);
        }
        if node.operands.len() > usize::from(u8::MAX) {
            return Err(ImageError::TooManyOperands);
        }
        let index =
            u32::try_from(self.nodes.len()).map_err(|_narrowing| ImageError::TooManyNodes)?;
        for &operand in &node.operands {
            if operand.0 >= index {
                return Err(ImageError::ForwardOperand(operand));
            }
        }
        self.nodes.push(node);
        Ok(NodeIndex(index))
    }
    /// Count static duplication and discard nodes separately.
    ///
    /// # Specification
    /// - ensures: each counter counts exactly its node kind, including both
    ///   case arms.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 unequal counts distinguish exchanged operation kinds.
    /// - witness: `tests::image::accounted_work_counts_each_kind_separately`
    #[spec(ensures: |ret| ret.duplications.0 >= 0 && ret.discards.0 >= 0)]
    #[must_use]
    #[inline]
    pub fn accounted_work(&self) -> AccountedWork
    {
        let mut work = AccountedWork::default();
        for node in &self.nodes {
            match node.kind {
                | NodeKind::Dup => work.duplications.0 = work.duplications.0.saturating_add(1),
                | NodeKind::Drop => work.discards.0 = work.discards.0.saturating_add(1),
                | _ => {},
            }
        }
        work
    }
    /// Classify dispatch presence for static-accounting consumers.
    ///
    /// # Specification
    /// - ensures: Present exactly when a node has kind Case.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 adding one case changes the accounting side condition.
    /// - witness: `tests::image::accounted_work_counts_each_kind_separately`
    #[spec(ensures: |ret| (ret == DispatchPresence::Present) == self.nodes.iter().any(|node| node.kind == NodeKind::Case))]
    #[must_use]
    #[inline]
    pub fn has_dispatch(&self) -> DispatchPresence
    {
        if self.nodes.iter().any(|node| node.kind == NodeKind::Case) {
            DispatchPresence::Present
        }
        else {
            DispatchPresence::Absent
        }
    }
    /// Encode version, node count and fixed-width records in little-endian
    /// order.
    ///
    /// # Specification
    /// - ensures: three header bytes precede each record's kind, tag, u32
    ///   binder, i64 literal, u8 operand count and ordered u32 operand
    ///   addresses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 a signed literal golden and distinct operands separate
    ///   byte order, field order, widths and count faults.
    /// - witness: `tests::image::the_wire_form_leads_with_its_version_and_node_count`
    /// - witness: `tests::contract::the_wire_numbering_matches_this_crates_mirror`
    #[spec(ensures: |ret| ret.0.first() == Some(&IMAGE_WIRE_VERSION))]
    #[must_use]
    #[inline]
    pub fn encode(&self) -> ImageBytes
    {
        let size = self.nodes.iter().fold(3_usize, |size, node| {
            size.saturating_add(15)
                .saturating_add(node.operands.len().saturating_mul(4))
        });
        let mut bytes = Vec::with_capacity(size);
        bytes.push(IMAGE_WIRE_VERSION);
        let count = u16::try_from(self.nodes.len()).unwrap_or(u16::MAX);
        bytes.extend_from_slice(&count.to_le_bytes());
        for node in &self.nodes {
            bytes.push(node.kind.wire_byte().0);
            bytes.push(node.tag.wire_byte().0);
            bytes.extend_from_slice(&node.binder.0.to_le_bytes());
            bytes.extend_from_slice(&node.literal.0.to_le_bytes());
            // push enforces the wire widths before a record enters the arena.
            bytes.push(u8::try_from(node.operands.len()).unwrap_or(u8::MAX));
            for operand in &node.operands {
                bytes.extend_from_slice(&operand.0.to_le_bytes());
            }
        }
        ImageBytes(bytes)
    }
}
