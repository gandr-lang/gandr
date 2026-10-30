//! The `cells` node, [`Cells`]: a composite or a filler written over named
//! cells, each cell a position in the tree the node was read from.
//!
//! The cells' types state the pasting shape a composite or a filler is read
//! at. The shape fixes the level, the stratum and the arity. A node that
//! recorded any of them would state the shape twice, and the two accounts
//! could disagree. So the node records none of them. It holds what the writer
//! wrote: the former, the motive a filler lifts, and the cells by name in the
//! writer's order. The pasting reading recovers the rest from the cells'
//! types.
//!
//! A cell is a name the context binds, `p`, or a name given a term,
//! `p = term`, as a substitution names the term it sends each variable to. A
//! cell is read by its name, never by its place in a tuple, so a cell keeps
//! its meaning when the shape around it changes.

use alloc::vec::Vec;
use core::fmt;

use crate::span::ByteSpan;
use crate::tree::NodeIndex;

/// The former a cells node writes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CellsKind
{
    /// `compose`: the composite of the cells.
    Compose,
    /// `fill`: the filler over the cells, which lifts the motive along them.
    Fill,
}

impl fmt::Display for CellsKind
{
    /// The former's keyword, `compose` or `fill`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Compose => "compose",
            Self::Fill => "fill",
        })
    }
}

/// One cell of a cells node: the name the writer gives it, and the term a
/// named substitution sends that name to.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct NamedCell
{
    /// The name's position.
    name: NodeIndex,
    /// The term's position, when the cell is written `name = term`.
    term: Option<NodeIndex>,
}

impl NamedCell
{
    /// The cell `name`, a name the context binds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bound(name: NodeIndex) -> Self
    {
        Self { name, term: None }
    }

    /// The cell `name = term`, a name given a term.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn given(
        name: NodeIndex,
        term: NodeIndex,
    ) -> Self
    {
        Self {
            name,
            term: Some(term),
        }
    }

    /// The name's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(self) -> NodeIndex
    {
        self.name
    }

    /// The term's position, or nothing when the context binds the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn term(self) -> Option<NodeIndex>
    {
        self.term
    }
}

/// A composite or a filler written over named cells: its former, the motive
/// a filler lifts, and the cells in the writer's order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Cells
{
    /// The bytes the node covers.
    span: ByteSpan,
    /// The former the node writes.
    kind: CellsKind,
    /// The motive's position, when the node writes one.
    motive: Option<NodeIndex>,
    /// The cells as written, in the writer's order.
    written: Vec<NamedCell>,
}

impl Cells
{
    /// The node `kind` over `written` at `span`, with `motive` when written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        span: ByteSpan,
        kind: CellsKind,
        motive: Option<NodeIndex>,
        written: Vec<NamedCell>,
    ) -> Self
    {
        Self {
            span,
            kind,
            motive,
            written,
        }
    }

    /// The bytes the node covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }

    /// The former the node writes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> CellsKind
    {
        self.kind
    }

    /// The motive's position, or nothing when the node writes none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn motive(&self) -> Option<NodeIndex>
    {
        self.motive
    }

    /// The cells, in the writer's order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(&self) -> &[NamedCell]
    {
        &self.written
    }
}
