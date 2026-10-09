//! The command-pattern language: the cut `⟨p |ε c⟩` over flat node tables,
//! with pattern metavariables, positions, subterm reading and splicing.
//!
//! A [`CmdPat`] is one cut: a [`Polarity`], a producer half [`ProdPat`] and a
//! consumer half [`ConsPat`]. Commands do not nest, so a cut is only ever the
//! root of a pattern.
//!
//! # Representation
//!
//! No pattern routes ownership through itself. A producer is one flat node
//! table: its nodes listed in reverse pre-order, the root last, every subtree
//! a contiguous index range ending at its own root, and each node's first
//! child immediately before it. Every node records its subtree's node count,
//! so a child is found by skipping its elder siblings' counts and a subtree is
//! read or copied as one slice. A consumer is a spine: the frames between the
//! cut and the consumer's end, listed innermost first, then the end itself —
//! the terminal `★` or a consumer metavariable. An operation frame's producer
//! arguments are producer tables of their own.
//!
//! The layout is canonical: two structurally equal patterns have equal tables,
//! so the derived [`Eq`] and [`Hash`] are structural content identity, and no
//! address, arena or session state enters either. Constructors compose in
//! place, reusing the buffer of the innermost part: wrapping a pattern in one
//! more constructor or frame appends to it rather than copying it.
//!
//! Every walk in this module and above it is a loop over a table or a spine,
//! or an explicit worklist; none recurses. A read past a table's end ends the
//! walk rather than panicking, and no constructor produces a table a walk can
//! read past.
//!
//! # Positions
//!
//! A [`Pos`] addresses a subterm as a path of child indices through the
//! uniform node view: a cut's children are its producer and then its
//! consumer; a constructor application's are its arguments; an operation
//! frame's are its arguments and then its return continuation; a return-side
//! constructor frame's is its return continuation. The empty path is the root.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::boundary::GroundPatternStatus;
use crate::boundary::PatternSize;
use crate::boundary::PositionRootStatus;
use crate::boundary::PositionStep;
use crate::polarity::Polarity;

/// A constructor or operation symbol: `Zero`, `Succ`, `add`, `Nil`, `Cons`.
///
/// Equality is by name, so a symbol is its own content key.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sym(Box<str>);

impl Sym
{
    /// A symbol from any name convertible into one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(name: N) -> Self
    where
        N: Into<Self>,
    {
        name.into()
    }
}

impl From<&str> for Sym
{
    /// A symbol spelled by the borrowed name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &str) -> Self
    {
        Self(value.into())
    }
}

impl From<String> for Sym
{
    /// A symbol spelled by the owned name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: String) -> Self
    {
        Self(value.into_boxed_str())
    }
}

impl AsRef<str> for Sym
{
    /// The symbol's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl core::fmt::Display for Sym
{
    /// Writes the symbol's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The name a hole is keyed by across a cell's two faces.
///
/// A name worn by a producer metavariable and by a consumer metavariable is
/// one hole at two polarities; the two metavariables stay distinct
/// substitution targets, because a [`MetaVar`] is the `(name, category)`
/// pair.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HoleName(Box<str>);

impl HoleName
{
    /// A hole name from any name convertible into one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(name: N) -> Self
    where
        N: Into<Self>,
    {
        name.into()
    }
}

impl From<&str> for HoleName
{
    /// A hole name spelled by the borrowed name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &str) -> Self
    {
        Self(value.into())
    }
}

impl From<String> for HoleName
{
    /// A hole name spelled by the owned name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: String) -> Self
    {
        Self(value.into_boxed_str())
    }
}

impl AsRef<str> for HoleName
{
    /// The hole name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl core::fmt::Display for HoleName
{
    /// Writes the hole name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The category a metavariable ranges over: the producer/consumer split of
/// the sequent grammar.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Cat
{
    /// A producer metavariable `x`, ranging over [`ProdPat`].
    Producer,
    /// A consumer metavariable `α`, ranging over [`ConsPat`].
    Consumer,
}

/// A pattern metavariable: a hole in a cell pattern, keyed by its
/// `(name, category)` pair.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MetaVar
{
    /// The hole's name.
    hole: HoleName,
    /// The category the metavariable ranges over.
    cat: Cat,
}

impl MetaVar
{
    /// The metavariable of `hole` at category `cat`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        hole: HoleName,
        cat: Cat,
    ) -> Self
    {
        Self { hole, cat }
    }

    /// A producer metavariable with the given name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn producer<N>(name: N) -> Self
    where
        N: Into<HoleName>,
    {
        Self::new(name.into(), Cat::Producer)
    }

    /// A consumer metavariable with the given name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn consumer<N>(name: N) -> Self
    where
        N: Into<HoleName>,
    {
        Self::new(name.into(), Cat::Consumer)
    }

    /// The hole's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hole(&self) -> &HoleName
    {
        &self.hole
    }

    /// The category the metavariable ranges over.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cat(&self) -> Cat
    {
        self.cat
    }
}

/// The number of producer arguments a constructor application or an operation
/// frame carries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArgumentCount(usize);

impl From<usize> for ArgumentCount
{
    /// Wraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<ArgumentCount> for usize
{
    /// Unwraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ArgumentCount) -> Self
    {
        value.0
    }
}

/// The head of one producer-table node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ProdHead
{
    /// A constructor application `K(p̄)` with its argument count.
    Ctor(Sym, ArgumentCount),
    /// A producer metavariable leaf.
    Meta(MetaVar),
}

impl ProdHead
{
    /// The node's number of children.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arity(&self) -> ArgumentCount
    {
        match *self {
            | Self::Ctor(_, arity) => arity,
            | Self::Meta(_) => ArgumentCount(0),
        }
    }
}

/// One node of a producer table: its head and the node count of the subtree
/// it roots.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ProdEntry
{
    /// The node's head.
    head: ProdHead,
    /// The node count of the subtree this node roots, itself included.
    extent: PatternSize,
}

impl ProdEntry
{
    /// The node's head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn head(&self) -> &ProdHead
    {
        &self.head
    }

    /// The node count of the subtree this node roots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn extent(&self) -> PatternSize
    {
        self.extent
    }
}

/// A producer pattern `p`: a metavariable or a constructor application, held
/// as one flat node table.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ProdPat
{
    /// Every node below the root, in reverse pre-order.
    below: Vec<ProdEntry>,
    /// The root node.
    root: ProdEntry,
}

impl ProdPat
{
    /// A producer metavariable pattern.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn meta<N>(name: N) -> Self
    where
        N: Into<HoleName>,
    {
        Self::leaf(ProdHead::Meta(MetaVar::producer(name)))
    }

    /// A constructor application `ctor(args)`.
    ///
    /// # Specification
    /// - ensures: the pattern whose root is `ctor` applied to `args` in order;
    ///   the last argument's table is reused as the new table's buffer, so
    ///   wrapping one argument costs one appended node.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn ctor<S, A>(
        ctor: S,
        args: A,
    ) -> Self
    where
        S: Into<Sym>,
        A: IntoIterator<Item = Self>,
    {
        let mut args: Vec<Self> = args.into_iter().collect();
        let arity = ArgumentCount(args.len());
        let mut below = match args.pop() {
            | Some(last) => {
                let mut below = last.below;
                below.push(last.root);
                below
            },
            | None => Vec::new(),
        };
        for arg in args.into_iter().rev() {
            below.extend(arg.below);
            below.push(arg.root);
        }
        let extent = PatternSize::from(below.len()).saturating_add(PatternSize::ONE);
        Self {
            below,
            root: ProdEntry {
                head: ProdHead::Ctor(ctor.into(), arity),
                extent,
            },
        }
    }

    /// A one-node table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn leaf(head: ProdHead) -> Self
    {
        Self {
            below: Vec::new(),
            root: ProdEntry {
                head,
                extent: PatternSize::ONE,
            },
        }
    }

    /// The pattern as a borrowed subtree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_ref(&self) -> ProdRef<'_>
    {
        ProdRef {
            below: &self.below,
            root: &self.root,
        }
    }

    /// The pattern's head and children.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> ProdView<'_>
    {
        self.to_ref().view()
    }

    /// The pattern's node count.
    ///
    /// # Specification
    /// - ensures: one per node; at least one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count is pinned exactly on a two-node producer,
    ///   beside the consumer and command counts it composes into.
    /// - witness: `pattern::tests::the_per_category_sizes_count_their_own_subtree`
    #[inline]
    #[must_use]
    pub fn size(&self) -> PatternSize
    {
        self.root.extent
    }

    /// Whether the pattern contains no metavariable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_ground(&self) -> GroundPatternStatus
    {
        self.to_ref().is_ground()
    }
}

/// `prod` with each metavariable leaf `lookup` answers for replaced by its
/// image.
///
/// # Specification
/// - ensures: the table rebuilt in index order: each answered leaf's image is
///   appended whole and each constructor's node count is one plus its
///   children's, which precede it; every other node is copied. The images are
///   inserted as given, one pass.
/// - panics: none.
/// - intension: one output table sized to the input; the pending child counts
///   are a stack, claimed by their parent as it is reached.
#[inline]
pub fn instantiate_prod<'image, L>(
    prod: ProdRef<'_>,
    lookup: &L,
) -> ProdPat
where
    L: Fn(&MetaVar) -> Maybe<ProdRef<'image>, crate::subst::binding::Absent>,
{
    if let ProdHead::Meta(ref var) = prod.root.head {
        return match lookup(var) {
            | Maybe::Present(image) => image.to_pattern(),
            | Maybe::Absent(_) => prod.to_pattern(),
        };
    }
    let mut below: Vec<ProdEntry> = Vec::with_capacity(prod.below.len());
    // The node counts of the completed subtrees not yet claimed by a parent,
    // the most recent last.
    let mut completed: Vec<PatternSize> = Vec::new();
    for entry in prod.below {
        match entry.head {
            | ProdHead::Meta(ref var) => match lookup(var) {
                | Maybe::Present(image) => {
                    below.extend(image.entries().cloned());
                    completed.push(image.size());
                },
                | Maybe::Absent(_) => {
                    below.push(entry.clone());
                    completed.push(PatternSize::ONE);
                },
            },
            | ProdHead::Ctor(_, arity) => {
                let first = completed.len().saturating_sub(arity.0);
                let extent = completed
                    .drain(first ..)
                    .fold(PatternSize::ONE, PatternSize::saturating_add);
                below.push(ProdEntry {
                    head: entry.head.clone(),
                    extent,
                });
                completed.push(extent);
            },
        }
    }
    // The root is a constructor over every node below it.
    let extent = PatternSize::from(below.len()).saturating_add(PatternSize::ONE);
    ProdPat {
        below,
        root: ProdEntry {
            head: prod.root.head.clone(),
            extent,
        },
    }
}

/// A borrowed producer subtree: a contiguous range of a producer table.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ProdRef<'pattern>
{
    /// Every node below the root, in reverse pre-order.
    below: &'pattern [ProdEntry],
    /// The subtree's root.
    root: &'pattern ProdEntry,
}

impl<'pattern> ProdRef<'pattern>
{
    /// The subtree's head and children.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(self) -> ProdView<'pattern>
    {
        match self.root.head {
            | ProdHead::Meta(ref var) => ProdView::Meta(var),
            | ProdHead::Ctor(ref ctor, _) => ProdView::Ctor {
                ctor,
                args: self.children(),
            },
        }
    }

    /// The subtree's root head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn head(self) -> &'pattern ProdHead
    {
        &self.root.head
    }

    /// The subtree's children, left to right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn children(self) -> ProdArgs<'pattern>
    {
        ProdArgs {
            rest: self.below,
            remaining: self.root.head.arity(),
        }
    }

    /// The subtree's node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn size(self) -> PatternSize
    {
        self.root.extent
    }

    /// Every node of the subtree, root first, in pre-order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn preorder(self) -> impl Iterator<Item = &'pattern ProdEntry>
    {
        core::iter::once(self.root).chain(self.below.iter().rev())
    }

    /// The subtree's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// - ensures: one item per metavariable leaf, in left-to-right order:
    ///   pre-order visits leaves left to right.
    /// - panics: none.
    #[inline]
    pub fn metavars(self) -> impl Iterator<Item = &'pattern MetaVar>
    {
        self.preorder().filter_map(|entry| match entry.head {
            | ProdHead::Meta(ref var) => Some(var),
            | ProdHead::Ctor(..) => None,
        })
    }

    /// Whether the subtree contains no metavariable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_ground(self) -> GroundPatternStatus
    {
        GroundPatternStatus::from(self.metavars().next().is_none())
    }

    /// An owned copy of the subtree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_pattern(self) -> ProdPat
    {
        ProdPat {
            below: self.below.to_vec(),
            root: self.root.clone(),
        }
    }

    /// Every node of the subtree in table order, the root last.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn entries(self) -> impl Iterator<Item = &'pattern ProdEntry>
    {
        self.below.iter().chain(core::iter::once(self.root))
    }

    /// The `step`-th child, with the offset of its first node from the start
    /// of this subtree's table range.
    ///
    /// # Specification
    /// - ensures: the child `step` counts from the left, and the number of this
    ///   subtree's nodes that precede the child's first node in the table.
    /// - provides: [`position_read::Absent::OffPattern`] when this node has no
    ///   child `step`.
    /// - panics: none.
    #[inline]
    fn nth_child(
        self,
        step: PositionStep,
    ) -> Maybe<(Self, TableOffset), position_read::Absent>
    {
        let mut children = self.children();
        let mut skipped = usize::from(step);
        loop {
            let Some(child) = children.next()
            else {
                return Maybe::Absent(position_read::Absent::OffPattern);
            };
            if skipped == 0 {
                return Maybe::Present((child, TableOffset(children.rest.len())));
            }
            skipped = skipped.saturating_sub(1);
        }
    }
}

/// A count of table nodes preceding a subtree's first node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct TableOffset(usize);

/// The head and children of one producer subtree.
#[derive(Clone, Debug)]
pub enum ProdView<'pattern>
{
    /// A producer metavariable `x`.
    Meta(&'pattern MetaVar),
    /// A constructor application `K(p̄)`.
    Ctor
    {
        /// The constructor symbol `K`.
        ctor: &'pattern Sym,
        /// The producer arguments `p̄`, left to right.
        args: ProdArgs<'pattern>,
    },
}

/// The children of a producer node, or the arguments of an operation frame,
/// left to right.
#[derive(Clone, Debug)]
pub struct ProdArgs<'pattern>
{
    /// The table range holding the children not yet yielded, the next one
    /// last.
    rest: &'pattern [ProdEntry],
    /// How many children remain.
    remaining: ArgumentCount,
}

impl<'pattern> Iterator for ProdArgs<'pattern>
{
    type Item = ProdRef<'pattern>;

    /// The next child.
    ///
    /// # Specification
    /// - ensures: yields the remaining children in left-to-right order; the
    ///   next child's root is the last node of `rest`, and its subtree the
    ///   `extent` nodes ending there. A range shorter than the extents it
    ///   records ends the iteration.
    /// - panics: none.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.remaining.0 == 0 {
            return None;
        }
        let (root, before) = self.rest.split_last()?;
        let below_len = usize::from(root.extent).checked_sub(1)?;
        let split = before.len().checked_sub(below_len)?;
        let (rest, below) = before.split_at_checked(split)?;
        self.rest = rest;
        self.remaining = ArgumentCount(self.remaining.0.saturating_sub(1));
        Some(ProdRef { below, root })
    }

    /// The exact number of remaining children.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        (self.remaining.0, Some(self.remaining.0))
    }
}

impl ExactSizeIterator for ProdArgs<'_>
{
}

/// One frame of a consumer spine.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SpineFrame
{
    /// An operation frame `f(p̄; c)`: an `f`-application waiting at the seam,
    /// with its remaining producer arguments.
    Op
    {
        /// The operation symbol `f`.
        op: Sym,
        /// The producer arguments `p̄`.
        args: Vec<ProdPat>,
    },
    /// A return-side constructor frame `K⁻(c)`, definable as
    /// `μ̃x.⟨K(x) | c⟩`; its defining cell is [`frame_defining_cell`].
    ///
    /// [`frame_defining_cell`]: crate::sequent::frame_defining_cell
    Frame(Sym),
}

/// Where a consumer spine ends.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SpineEnd
{
    /// The terminal consumer `★`.
    Top,
    /// A consumer metavariable `α`.
    Meta(MetaVar),
}

/// A consumer pattern `c`: a spine of frames ending in the terminal `★` or a
/// consumer metavariable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ConsPat
{
    /// The frames, innermost first: the last frame meets the cut.
    frames: Vec<SpineFrame>,
    /// The end of the spine, inside the innermost frame.
    end: SpineEnd,
}

impl ConsPat
{
    /// A consumer metavariable pattern.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn meta<N>(name: N) -> Self
    where
        N: Into<HoleName>,
    {
        Self {
            frames: Vec::new(),
            end: SpineEnd::Meta(MetaVar::consumer(name)),
        }
    }

    /// The terminal consumer `★`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn top() -> Self
    {
        Self {
            frames: Vec::new(),
            end: SpineEnd::Top,
        }
    }

    /// An operation frame `op(args; ret)`.
    ///
    /// # Specification
    /// - ensures: the consumer whose outermost frame is `op` over `args` in
    ///   order, continuing as `ret`; `ret`'s spine is reused as the new spine's
    ///   buffer.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn op<S, A>(
        op: S,
        args: A,
        ret: Self,
    ) -> Self
    where
        S: Into<Sym>,
        A: IntoIterator<Item = ProdPat>,
    {
        let mut frames = ret.frames;
        frames.push(SpineFrame::Op {
            op: op.into(),
            args: args.into_iter().collect(),
        });
        Self {
            frames,
            end: ret.end,
        }
    }

    /// A return-side constructor frame `ctor⁻(ret)`.
    ///
    /// # Specification
    /// - ensures: the consumer whose outermost frame re-wraps with `ctor`,
    ///   continuing as `ret`; `ret`'s spine is reused as the new spine's
    ///   buffer.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn frame<S>(
        ctor: S,
        ret: Self,
    ) -> Self
    where
        S: Into<Sym>,
    {
        let mut frames = ret.frames;
        frames.push(SpineFrame::Frame(ctor.into()));
        Self {
            frames,
            end: ret.end,
        }
    }

    /// The pattern as a borrowed subtree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_ref(&self) -> ConsRef<'_>
    {
        ConsRef {
            frames: &self.frames,
            end: &self.end,
        }
    }

    /// The pattern's outermost frame and continuation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> ConsView<'_>
    {
        self.to_ref().view()
    }

    /// The pattern's node count: one per frame, per argument node and for the
    /// end.
    ///
    /// # Specification
    /// - ensures: each frame counts one plus its arguments' node counts, and
    ///   the end counts one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count is pinned exactly on an operation frame
    ///   with one argument and a metavariable end.
    /// - witness: `pattern::tests::the_per_category_sizes_count_their_own_subtree`
    #[inline]
    #[must_use]
    pub fn size(&self) -> PatternSize
    {
        self.to_ref().size()
    }

    /// Whether the pattern contains no metavariable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_ground(&self) -> GroundPatternStatus
    {
        GroundPatternStatus::from(self.to_ref().metavars().next().is_none())
    }

    /// A spine from its frames, innermost first, and its end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn from_parts(
        frames: Vec<SpineFrame>,
        end: SpineEnd,
    ) -> Self
    {
        Self { frames, end }
    }
}

/// A borrowed consumer subtree: a suffix of a spine.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ConsRef<'pattern>
{
    /// The frames from the end up to this suffix's outermost, innermost
    /// first.
    frames: &'pattern [SpineFrame],
    /// The spine's end.
    end: &'pattern SpineEnd,
}

impl<'pattern> ConsRef<'pattern>
{
    /// The subtree's outermost frame and continuation.
    ///
    /// # Specification
    /// - ensures: the outermost frame with its continuation one frame in, or
    ///   the end when no frame remains.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn view(self) -> ConsView<'pattern>
    {
        let Some((outer, inner)) = self.frames.split_last()
        else {
            return match *self.end {
                | SpineEnd::Top => ConsView::Top,
                | SpineEnd::Meta(ref var) => ConsView::Meta(var),
            };
        };
        let ret = ConsRef {
            frames: inner,
            end: self.end,
        };
        match *outer {
            | SpineFrame::Op { ref op, ref args } => ConsView::Op {
                op,
                args: OpArgs(args.iter()),
                ret,
            },
            | SpineFrame::Frame(ref ctor) => ConsView::Frame { ctor, ret },
        }
    }

    /// The frames of this suffix, innermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn frames(self) -> &'pattern [SpineFrame]
    {
        self.frames
    }

    /// The spine's end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(self) -> &'pattern SpineEnd
    {
        self.end
    }

    /// The subtree's node count.
    ///
    /// # Specification
    /// - ensures: each frame counts one plus its arguments' node counts, and
    ///   the end counts one.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn size(self) -> PatternSize
    {
        let mut size = PatternSize::ONE;
        for frame in self.frames {
            size = size.saturating_add(PatternSize::ONE);
            if let SpineFrame::Op { ref args, .. } = *frame {
                for arg in args {
                    size = size.saturating_add(arg.size());
                }
            }
        }
        size
    }

    /// The subtree's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// - ensures: one item per metavariable occurrence, outermost frame first,
    ///   each operation frame's arguments in order, then the end.
    /// - panics: none.
    #[inline]
    pub fn metavars(self) -> impl Iterator<Item = &'pattern MetaVar>
    {
        let args = self.frames.iter().rev().flat_map(|frame| match *frame {
            | SpineFrame::Op { ref args, .. } => args.as_slice(),
            | SpineFrame::Frame(_) => &[],
        });
        let end = match *self.end {
            | SpineEnd::Meta(ref var) => Some(var),
            | SpineEnd::Top => None,
        };
        args.flat_map(|arg| arg.to_ref().metavars()).chain(end)
    }

    /// An owned copy of the subtree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_pattern(self) -> ConsPat
    {
        ConsPat {
            frames: self.frames.to_vec(),
            end: self.end.clone(),
        }
    }

    /// Whether this suffix is a bare metavariable, with no frame above its
    /// end.
    ///
    /// # Specification
    /// - provides: [`bare_end::Absent::Framed`] when a frame remains,
    ///   [`bare_end::Absent::Terminal`] when the end is `★`.
    /// - panics: none.
    #[inline]
    pub fn bare_meta(self) -> Maybe<&'pattern MetaVar, bare_end::Absent>
    {
        if !self.frames.is_empty() {
            return Maybe::Absent(bare_end::Absent::Framed);
        }
        match *self.end {
            | SpineEnd::Meta(ref var) => Maybe::Present(var),
            | SpineEnd::Top => Maybe::Absent(bare_end::Absent::Terminal),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a consumer suffix is not a bare metavariable.
    pub mod bare_end {
        /// The reason the suffix is something else.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A frame sits above the end.
            Framed,
            /// The end is the terminal `★`.
            Terminal,
        }
    }
}

/// The outermost frame and continuation of one consumer subtree.
#[derive(Clone, Debug)]
pub enum ConsView<'pattern>
{
    /// A consumer metavariable `α`.
    Meta(&'pattern MetaVar),
    /// An operation frame `f(p̄; c)`.
    Op
    {
        /// The operation symbol `f`.
        op: &'pattern Sym,
        /// The producer arguments `p̄`, left to right.
        args: OpArgs<'pattern>,
        /// The return continuation `c`.
        ret: ConsRef<'pattern>,
    },
    /// A return-side constructor frame `K⁻(c)`.
    Frame
    {
        /// The constructor symbol `K` the frame re-wraps with.
        ctor: &'pattern Sym,
        /// The return continuation `c`.
        ret: ConsRef<'pattern>,
    },
    /// The terminal consumer `★`.
    Top,
}

/// The producer arguments of an operation frame, left to right.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct OpArgs<'pattern>(core::slice::Iter<'pattern, ProdPat>);

impl<'pattern> Iterator for OpArgs<'pattern>
{
    type Item = ProdRef<'pattern>;

    /// The next argument.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(ProdPat::to_ref)
    }

    /// The exact number of remaining arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for OpArgs<'_>
{
}

/// A command pattern `s`: one cut `⟨p |ε c⟩` carrying its polarity.
///
/// The `prim` and `jump` commands of the sequent language are outside the
/// cell-visible fragment: a primitive is an opaque host seam and a jump
/// carries no seam a cell reads through.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CmdPat
{
    /// The cut's orientation `ε`.
    polarity: Polarity,
    /// The producer half `p`.
    prod: ProdPat,
    /// The consumer half `c`.
    cons: ConsPat,
}

impl CmdPat
{
    /// A cut pattern `⟨prod |polarity cons⟩`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cut(
        polarity: Polarity,
        prod: ProdPat,
        cons: ConsPat,
    ) -> Self
    {
        Self {
            polarity,
            prod,
            cons,
        }
    }

    /// The cut's polarity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn polarity(&self) -> Polarity
    {
        self.polarity
    }

    /// The producer half.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn producer(&self) -> &ProdPat
    {
        &self.prod
    }

    /// The consumer half.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn consumer(&self) -> &ConsPat
    {
        &self.cons
    }

    /// The pattern's node count, the cut included.
    ///
    /// # Specification
    /// - ensures: one for the cut plus the two halves' node counts; a positive
    ///   count, monotone under subterm inclusion.
    /// - provides: the well-founded measure the reduction order compares before
    ///   it consults the path order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count is pinned exactly on a three-node ground
    ///   cut, and on a cut against the sum of its two halves.
    /// - witness: `pattern::tests::ground_and_size_track_structure`
    /// - witness: `pattern::tests::the_per_category_sizes_count_their_own_subtree`
    #[inline]
    #[must_use]
    pub fn size(&self) -> PatternSize
    {
        PatternSize::ONE
            .saturating_add(self.prod.size())
            .saturating_add(self.cons.size())
    }

    /// Whether the pattern is ground: the shape a machine configuration and a
    /// differential instance take.
    ///
    /// # Specification
    /// - ensures: positive exactly when no metavariable leaf occurs.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one pattern with metavariables and one ground cut
    ///   separate the two answers.
    /// - witness: `pattern::tests::ground_and_size_track_structure`
    #[inline]
    #[must_use]
    pub fn is_ground(&self) -> GroundPatternStatus
    {
        GroundPatternStatus::from(self.metavars().next().is_none())
    }

    /// The pattern's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// - ensures: one item per metavariable occurrence, the producer half
    ///   first, then the consumer half outermost frame first, so linearity is
    ///   judged by counting.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the order is pinned on one cut carrying a producer,
    ///   an operation-argument and a return metavariable.
    /// - witness: `pattern::tests::metavars_are_collected_in_order`
    #[inline]
    pub fn metavars(&self) -> impl Iterator<Item = &MetaVar>
    {
        self.prod
            .to_ref()
            .metavars()
            .chain(self.cons.to_ref().metavars())
    }
}

/// A pattern subterm of any category, owned.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Node
{
    /// A producer subterm.
    Prod(ProdPat),
    /// A consumer subterm.
    Cons(ConsPat),
    /// A command subterm.
    Cmd(CmdPat),
}

impl Node
{
    /// The subterm as a borrowed view.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_ref(&self) -> NodeRef<'_>
    {
        match *self {
            | Self::Prod(ref prod) => NodeRef::Prod(prod.to_ref()),
            | Self::Cons(ref cons) => NodeRef::Cons(cons.to_ref()),
            | Self::Cmd(ref cmd) => NodeRef::Cmd(cmd),
        }
    }
}

/// A pattern subterm of any category, borrowed.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum NodeRef<'pattern>
{
    /// A producer subterm.
    Prod(ProdRef<'pattern>),
    /// A consumer subterm.
    Cons(ConsRef<'pattern>),
    /// A command subterm.
    Cmd(&'pattern CmdPat),
}

impl NodeRef<'_>
{
    /// An owned copy of the subterm.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(self) -> Node
    {
        match self {
            | Self::Prod(prod) => Node::Prod(prod.to_pattern()),
            | Self::Cons(cons) => Node::Cons(cons.to_pattern()),
            | Self::Cmd(cmd) => Node::Cmd(cmd.clone()),
        }
    }

    /// The `step`-th child, counted from the left in the uniform node view.
    ///
    /// # Specification
    /// - ensures: a cut's children are its producer then its consumer; a
    ///   constructor's its arguments; an operation frame's its arguments then
    ///   its return continuation; a return-side frame's its continuation.
    /// - provides: [`position_read::Absent::OffPattern`] when the node has no
    ///   child `step`.
    /// - panics: none.
    #[inline]
    fn child(
        self,
        step: PositionStep,
    ) -> Maybe<Self, position_read::Absent>
    {
        let index = usize::from(step);
        match self {
            | Self::Cmd(cmd) => match index {
                | 0 => Maybe::Present(Self::Prod(cmd.prod.to_ref())),
                | 1 => Maybe::Present(Self::Cons(cmd.cons.to_ref())),
                | _ => Maybe::Absent(position_read::Absent::OffPattern),
            },
            | Self::Prod(prod) => prod.nth_child(step).map(|(child, _)| Self::Prod(child)),
            | Self::Cons(cons) => match cons.view() {
                | ConsView::Op { mut args, ret, .. } => {
                    let arity = args.len();
                    if index == arity {
                        Maybe::Present(Self::Cons(ret))
                    }
                    else {
                        match args.nth(index) {
                            | Some(arg) => Maybe::Present(Self::Prod(arg)),
                            | None => Maybe::Absent(position_read::Absent::OffPattern),
                        }
                    }
                },
                | ConsView::Frame { ret, .. } if index == 0 => Maybe::Present(Self::Cons(ret)),
                | ConsView::Frame { .. } | ConsView::Meta(_) | ConsView::Top => {
                    Maybe::Absent(position_read::Absent::OffPattern)
                },
            },
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a position addresses no subterm of a pattern.
    pub mod position_read {
        /// The reason the read finds nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A step indexes past a node's children.
            OffPattern,
        }
    }
}

/// A position: a path of child indices from the root, through the uniform
/// node view.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Pos(Box<[PositionStep]>);

impl Pos
{
    /// The root position, the empty path.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root() -> Self
    {
        Self(Box::from([]))
    }

    /// The position whose path is `steps`, read from the root outward.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn from_steps<I>(steps: I) -> Self
    where
        I: IntoIterator<Item = PositionStep>,
    {
        Self(steps.into_iter().collect())
    }

    /// Whether this is the root position.
    ///
    /// # Specification
    /// - ensures: positive exactly for the empty path.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty path and a one-step path separate the two
    ///   answers.
    /// - witness: `pattern::tests::the_root_position_is_the_only_one_that_reports_root`
    #[inline]
    #[must_use]
    pub fn is_root(&self) -> PositionRootStatus
    {
        PositionRootStatus::from(self.0.is_empty())
    }

    /// This position extended by one child step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn child(
        &self,
        step: PositionStep,
    ) -> Self
    {
        let mut next = Vec::with_capacity(self.0.len().saturating_add(1));
        next.extend_from_slice(&self.0);
        next.push(step);
        Self(next.into_boxed_slice())
    }

    /// The path's steps, from the root outward.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[PositionStep]
    {
        &self.0
    }
}

/// The subterm `pos` addresses in `root`.
///
/// # Specification
/// - ensures: the subterm reached by following each step of `pos` from `root`
///   through the uniform node view; the root itself for the empty path.
/// - provides: [`position_read::Absent::OffPattern`] when a step indexes past a
///   node's children.
/// - panics: none.
/// - intension: borrows; the walk is one loop over the path, and each step
///   skips at most the elder siblings of the child it takes.
///
/// # Adequacy
/// - hypothesis: L3 — an operation argument two steps down is read exactly, and
///   the deep-pattern witness reads the end of a spine many thousands of frames
///   down.
/// - witness: `pattern::tests::subterm_and_splice_round_trip`
/// - witness: `tests::depth::a_deep_pattern_is_matched_ordered_and_dropped_on_a_small_stack`
#[inline]
pub fn subterm_at<'pattern>(
    root: NodeRef<'pattern>,
    pos: &Pos,
) -> Maybe<NodeRef<'pattern>, position_read::Absent>
{
    let mut cursor = root;
    for &step in pos.steps() {
        cursor = match cursor.child(step) {
            | Maybe::Present(child) => child,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
    }
    Maybe::Present(cursor)
}

/// A refused splice.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SpliceRefusal
{
    /// A step of the position indexes past a node's children.
    OffPattern,
    /// The replacement's category is not the category of the subterm it
    /// would replace: a consumer cannot fill a producer slot.
    CategoryMismatch,
}

impl core::fmt::Display for SpliceRefusal
{
    /// Names the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::OffPattern => "the position addresses no subterm of the pattern",
            | Self::CategoryMismatch => {
                "the replacement's category differs from the subterm it would replace"
            },
        })
    }
}

impl core::error::Error for SpliceRefusal
{
}

/// `root` with the subterm at `pos` replaced by `replacement`.
///
/// # Specification
/// - ensures: the pattern equal to `root` everywhere except at `pos`, where it
///   holds `replacement`; reading `pos` in the result returns `replacement`.
/// - fails: [`SpliceRefusal::OffPattern`] when a step of `pos` indexes past a
///   node's children; [`SpliceRefusal::CategoryMismatch`] when the subterm at
///   `pos` and `replacement` differ in category. Nothing is grafted on refusal.
/// - panics: none.
/// - intension: one walk down the path, then one copy of the table or spine the
///   subterm sits in, with the ancestors' node counts adjusted.
///
/// # Errors
/// - [`SpliceRefusal::OffPattern`]: `pos` leaves `root`.
/// - [`SpliceRefusal::CategoryMismatch`]: `replacement` cannot fill the slot.
///
/// # Adequacy
/// - hypothesis: L3 — a producer spliced into an operation argument is asserted
///   exactly, a consumer offered for that slot is refused by its variant, and
///   the deep-pattern witness splices at the end of a spine many thousands of
///   frames down.
/// - witness: `pattern::tests::subterm_and_splice_round_trip`
/// - witness: `pattern::tests::a_miscategorized_splice_is_rejected`
/// - witness: `tests::depth::a_deep_pattern_is_matched_ordered_and_dropped_on_a_small_stack`
#[inline]
pub fn splice_at(
    root: NodeRef<'_>,
    pos: &Pos,
    replacement: Node,
) -> Result<Node, SpliceRefusal>
{
    match root {
        | NodeRef::Cmd(cmd) => {
            let spliced = splice_cmd(cmd, pos, replacement)?;
            Ok(Node::Cmd(spliced))
        },
        | NodeRef::Prod(prod) => {
            let spliced = splice_prod(prod, pos.steps(), replacement)?;
            Ok(Node::Prod(spliced))
        },
        | NodeRef::Cons(cons) => {
            let spliced = splice_cons(cons, pos.steps(), replacement)?;
            Ok(Node::Cons(spliced))
        },
    }
}

/// `cmd` with the subterm at `pos` replaced by `replacement`, still a
/// command.
///
/// # Specification
/// - ensures: as [`splice_at`], for a command root: the result is a command
///   whatever subterm `pos` addresses, and at the root position it is
///   `replacement` itself.
/// - fails: as [`splice_at`]; at the root position a replacement that is not a
///   command is a [`SpliceRefusal::CategoryMismatch`].
/// - panics: none.
/// - intension: the half the path leaves untouched is copied once, the other is
///   rebuilt once.
///
/// # Errors
/// As [`splice_at`].
///
/// # Adequacy
/// - hypothesis: L3 — the round-trip and miscategorized witnesses splice into a
///   command root; the inhabitant suite of `gandr-theory-cell-complexes-tools`
///   splices a command back at the root through the alphabet interface.
/// - witness: `pattern::tests::subterm_and_splice_round_trip`
/// - witness: `pattern::tests::a_miscategorized_splice_is_rejected`
#[inline]
pub fn splice_cmd(
    cmd: &CmdPat,
    pos: &Pos,
    replacement: Node,
) -> Result<CmdPat, SpliceRefusal>
{
    let Some((&first, rest)) = pos.steps().split_first()
    else {
        return match replacement {
            | Node::Cmd(replacement) => Ok(replacement),
            | Node::Prod(_) | Node::Cons(_) => Err(SpliceRefusal::CategoryMismatch),
        };
    };
    match usize::from(first) {
        | 0 => {
            let prod = splice_prod(cmd.prod.to_ref(), rest, replacement)?;
            Ok(CmdPat::cut(cmd.polarity, prod, cmd.cons.clone()))
        },
        | 1 => {
            let cons = splice_cons(cmd.cons.to_ref(), rest, replacement)?;
            Ok(CmdPat::cut(cmd.polarity, cmd.prod.clone(), cons))
        },
        | _ => Err(SpliceRefusal::OffPattern),
    }
}

/// `prod` with the subterm at `steps` replaced.
///
/// # Specification
/// - ensures: as [`splice_at`], for a producer root.
/// - fails: as [`splice_at`].
/// - panics: none.
///
/// # Errors
/// As [`splice_at`].
fn splice_prod(
    prod: ProdRef<'_>,
    steps: &[PositionStep],
    replacement: Node,
) -> Result<ProdPat, SpliceRefusal>
{
    let Node::Prod(replacement) = replacement
    else {
        let at_slot = descend_prod(prod, steps);
        return Err(match at_slot {
            | Maybe::Present(_) => SpliceRefusal::CategoryMismatch,
            | Maybe::Absent(position_read::Absent::OffPattern) => SpliceRefusal::OffPattern,
        });
    };
    let (target, start, ancestors) = match descend_prod(prod, steps) {
        | Maybe::Present(found) => found,
        | Maybe::Absent(position_read::Absent::OffPattern) => {
            return Err(SpliceRefusal::OffPattern);
        },
    };
    if steps.is_empty() {
        return Ok(replacement);
    }
    let removed_size = target.size();
    let added_size = replacement.size();
    let removed = usize::from(removed_size);
    let added = usize::from(added_size);
    let mut below: Vec<ProdEntry> = Vec::with_capacity(
        prod.below
            .len()
            .saturating_sub(removed)
            .saturating_add(added),
    );
    let start = start.0;
    let end = start.saturating_add(removed);
    below.extend(prod.below.iter().take(start).cloned());
    below.extend(replacement.below);
    below.push(replacement.root);
    below.extend(prod.below.iter().skip(end).cloned());
    // Every ancestor below the root sits after the spliced range; its index
    // moves by the size difference and its extent grows or shrinks by it.
    for ancestor in ancestors {
        let shifted = ancestor.0.saturating_sub(removed).saturating_add(added);
        if let Some(entry) = below.get_mut(shifted) {
            entry.extent = entry
                .extent
                .saturating_sub(removed_size)
                .saturating_add(added_size);
        }
    }
    let extent = PatternSize::from(below.len()).saturating_add(PatternSize::ONE);
    Ok(ProdPat {
        below,
        root: ProdEntry {
            head: prod.root.head.clone(),
            extent,
        },
    })
}

/// The index, within a producer table's below-root range, of one node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct BelowIndex(usize);

/// The subtree `steps` addresses in `prod`, the index of its first node, and
/// the below-root indices of its proper ancestors other than the root.
///
/// # Specification
/// - ensures: the subtree reached along `steps`; its first node's index in
///   `prod`'s below-root range; and, for every ancestor strictly between the
///   root and the subtree, that ancestor's index in the same range.
/// - provides: [`position_read::Absent::OffPattern`] when a step indexes past a
///   node's children.
/// - panics: none.
fn descend_prod<'pattern>(
    prod: ProdRef<'pattern>,
    steps: &[PositionStep],
) -> Maybe<(ProdRef<'pattern>, TableOffset, Vec<BelowIndex>), position_read::Absent>
{
    let mut cursor = prod;
    let mut start = 0_usize;
    let mut ancestors: Vec<BelowIndex> = Vec::with_capacity(steps.len());
    for (depth, &step) in steps.iter().enumerate() {
        if depth > 0 {
            // The cursor is a proper descendant of the root: record its root's
            // index, which is its last node.
            let root_index = start
                .saturating_add(usize::from(cursor.size()))
                .saturating_sub(1);
            ancestors.push(BelowIndex(root_index));
        }
        let (child, offset) = match cursor.nth_child(step) {
            | Maybe::Present(found) => found,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        start = start.saturating_add(offset.0);
        cursor = child;
    }
    Maybe::Present((cursor, TableOffset(start), ancestors))
}

/// `cons` with the subterm at `steps` replaced.
///
/// # Specification
/// - ensures: as [`splice_at`], for a consumer root.
/// - fails: as [`splice_at`].
/// - panics: none.
///
/// # Errors
/// As [`splice_at`].
fn splice_cons(
    cons: ConsRef<'_>,
    steps: &[PositionStep],
    replacement: Node,
) -> Result<ConsPat, SpliceRefusal>
{
    // Walk the spine from the outside. `depth` frames have been entered; an
    // operation argument step leaves the spine for a producer table.
    let mut cursor = cons;
    let mut depth = SpineDepth(0);
    for (index, &step) in steps.iter().enumerate() {
        let step_index = usize::from(step);
        match cursor.view() {
            | ConsView::Op { args, ret, .. } => {
                let arity = args.len();
                if step_index == arity {
                    cursor = ret;
                    depth = SpineDepth(depth.0.saturating_add(1));
                    continue;
                }
                if step_index > arity {
                    return Err(SpliceRefusal::OffPattern);
                }
                let rest = steps.get(index.saturating_add(1) ..).unwrap_or(&[]);
                return splice_op_argument(cons, depth, step, rest, replacement);
            },
            | ConsView::Frame { ret, .. } if step_index == 0 => {
                cursor = ret;
                depth = SpineDepth(depth.0.saturating_add(1));
            },
            | ConsView::Frame { .. } | ConsView::Meta(_) | ConsView::Top => {
                return Err(SpliceRefusal::OffPattern);
            },
        }
    }
    let Node::Cons(replacement) = replacement
    else {
        return Err(SpliceRefusal::CategoryMismatch);
    };
    // Keep the outer `depth` frames and continue as the replacement inside
    // them; the frames are listed innermost first.
    let kept = cons.frames.len().saturating_sub(depth.0);
    let mut frames = replacement.frames;
    frames.extend(cons.frames.iter().skip(kept).cloned());
    Ok(ConsPat {
        frames,
        end: replacement.end,
    })
}

/// `cons` with the subterm at `rest` inside one operation argument replaced.
///
/// # Specification
/// - requires: the frame `depth` frames in from the outside of `cons` is an
///   operation frame with an argument `argument`.
/// - ensures: as [`splice_at`], for that argument's producer table.
/// - fails: as [`splice_at`]; [`SpliceRefusal::OffPattern`] when the
///   requirement does not hold.
/// - panics: none.
///
/// # Errors
/// As [`splice_at`].
fn splice_op_argument(
    cons: ConsRef<'_>,
    depth: SpineDepth,
    argument: PositionStep,
    rest: &[PositionStep],
    replacement: Node,
) -> Result<ConsPat, SpliceRefusal>
{
    let mut rebuilt = cons.to_pattern();
    let frame_index = rebuilt
        .frames
        .len()
        .checked_sub(depth.0.saturating_add(1))
        .ok_or(SpliceRefusal::OffPattern)?;
    let Some(&mut SpineFrame::Op { ref mut args, .. }) = rebuilt.frames.get_mut(frame_index)
    else {
        return Err(SpliceRefusal::OffPattern);
    };
    let slot = args
        .get_mut(usize::from(argument))
        .ok_or(SpliceRefusal::OffPattern)?;
    let spliced = splice_prod(slot.to_ref(), rest, replacement)?;
    *slot = spliced;
    Ok(rebuilt)
}

/// How many frames a walk has entered from a spine's outside.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct SpineDepth(usize);

#[cfg(test)]
mod tests
{
    use super::*;

    /// `⟨Succ(m) | add(n; α)⟩`: the Peano successor rule's left-hand side.
    ///
    /// # Specification
    /// trivial.
    fn peano_add_s() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        )
    }

    #[test]
    fn metavars_are_collected_in_order()
    {
        let cmd = peano_add_s();
        let names: Vec<&str> = cmd.metavars().map(|var| var.hole().as_ref()).collect();
        assert_eq!(
            &["m", "n", "alpha"][..],
            names.as_slice(),
            "producer then op-arg then ret"
        );
    }

    #[test]
    fn ground_and_size_track_structure()
    {
        assert!(
            !bool::from(peano_add_s().is_ground()),
            "the rule LHS has metavars"
        );
        let ground = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        assert!(
            bool::from(ground.is_ground()),
            "Zero cut against Top is ground"
        );
        assert_eq!(
            PatternSize::from(3_usize),
            ground.size(),
            "cut + Zero + Top"
        );
    }

    #[test]
    fn subterm_and_splice_round_trip()
    {
        let root = Node::Cmd(peano_add_s());
        // Position [1, 0] = the op's first producer argument `n`.
        let pos = Pos::from_steps([1_usize, 0_usize].map(PositionStep::from));
        let Maybe::Present(sub) = subterm_at(root.to_ref(), &pos)
        else {
            panic!("n is addressable");
        };
        assert_eq!(
            sub.to_node(),
            Node::Prod(ProdPat::meta("n")),
            "reached the op arg"
        );
        let spliced = splice_at(root.to_ref(), &pos, Node::Prod(ProdPat::ctor("Zero", [])))
            .expect("a producer splices into a producer slot");
        let expected = Node::Cmd(CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::meta("alpha")),
        ));
        assert_eq!(spliced, expected, "the op arg was replaced by Zero");
    }

    #[test]
    fn a_miscategorized_splice_is_rejected()
    {
        let root = Node::Cmd(peano_add_s());
        let pos = Pos::from_steps([1_usize, 0_usize].map(PositionStep::from));
        // A consumer cannot fill a producer slot.
        assert_eq!(
            Err(SpliceRefusal::CategoryMismatch),
            splice_at(root.to_ref(), &pos, Node::Cons(ConsPat::top())),
            "grafting a consumer where a producer belongs is declined"
        );
    }

    #[test]
    fn the_root_position_is_the_only_one_that_reports_root()
    {
        assert!(
            bool::from(Pos::root().is_root()),
            "the empty path is the root"
        );
        assert!(
            !bool::from(Pos::from_steps([PositionStep::from(0_usize)]).is_root()),
            "and one step down is not"
        );
    }

    #[test]
    fn the_per_category_sizes_count_their_own_subtree()
    {
        // The three size faces agree on one term: a cut is its two halves plus
        // itself, so the whole exceeds each part by more than one only because
        // the parts are counted whole.
        let cmd = peano_add_s();
        let producer = cmd.producer().size();
        let consumer = cmd.consumer().size();
        assert_eq!(
            PatternSize::from(2_usize),
            producer,
            "`Succ(m)` is the constructor and its argument"
        );
        assert_eq!(
            PatternSize::from(3_usize),
            consumer,
            "`add(n; α)` is the frame, its argument, and its return continuation"
        );
        assert_eq!(
            producer
                .saturating_add(consumer)
                .saturating_add(PatternSize::ONE),
            cmd.size(),
            "and the cut is both halves plus itself"
        );
    }
}
