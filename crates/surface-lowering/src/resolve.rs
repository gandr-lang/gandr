//! Name resolution: [`SurfaceName`], the two type-head tables, and the binder
//! [`Scope`] a lambda extends.
//!
//! # Type heads are identifiers, resolved through a table
//!
//! `Unit`, `Integer`, `String`, `+U` and `-F` resolve through a table, exactly
//! as a term name resolves through the declaration table. The grammar lexes
//! some of them as keywords of their own forms, but the lowering still reads
//! each head's spelling and asks the table: a misspelled head is an unresolved
//! head with a span, never a parse refusal and never an opaque atom.
//!
//! # The table is indexed by arity, and the arity is positional
//!
//! A head written bare answers from the nullary table; a head applied to one
//! argument answers from the unary table; a head applied to more answers from
//! nothing, because the fragment has no former of two arguments. Nothing
//! pushes an expected sort down into the lookup: a head *determines* the sort
//! it produces — `+U` a value type, `-F` a computation type — and whether that
//! sort suits the position is decided where the produced node stands.
//!
//! # Two scopes, innermost first
//!
//! A term name resolves against the enclosing lambda binders, then against the
//! module's declarations strictly earlier than the one being lowered. Nothing
//! falls through: a name neither scope answers is a refusal, and there is no
//! atom former reachable from name resolution. The unit value is the empty
//! parentheses `()`, a form of its own, so no name is reserved for it.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::error::LoweringRefusal;
use crate::lower::Fuel;

quenchant_shape::reason_enum! {
    /// Why a type-head table answers nothing for a spelling.
    pub mod type_head {
        /// The table holds no entry for the spelling.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No entry of this table is spelled so.
            Unregistered,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the binder scope answers nothing for a name.
    pub mod binder {
        /// No enclosing binder carries the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The chain was walked to its outermost frame without a match.
            Unbound,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a binder carries no written type.
    pub mod binder_type {
        /// The binder was written without `: T`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A lambda's binder, a statement's, or a parameter written untyped.
            Untyped,
        }
    }
}

/// An identifier as the source wrote it, at whatever sort its position gives
/// it.
///
/// Deliberately a wrapper over [`SourceFragment`] rather than over the source
/// itself: a name is the bytes one node covers and carries no offset frame, so
/// it can never be read back as the text a span is measured against.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SurfaceName<'source>(SourceFragment<'source>);

impl<'source> From<SourceFragment<'source>> for SurfaceName<'source>
{
    /// The name spelled by `fragment`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fragment: SourceFragment<'source>) -> Self
    {
        Self(fragment)
    }
}

impl<'source> From<&'source str> for SurfaceName<'source>
{
    /// The name spelled by `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'source str) -> Self
    {
        Self(SourceFragment::from(text))
    }
}

impl<'source> From<SurfaceName<'source>> for SourceFragment<'source>
{
    /// The bytes `name` covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: SurfaceName<'source>) -> Self
    {
        name.0
    }
}

impl AsRef<str> for SurfaceName<'_>
{
    /// The name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_ref()
    }
}

impl fmt::Display for SurfaceName<'_>
{
    /// Writes the name as the source spelled it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.as_ref())
    }
}

/// A number of operands, arguments or parameters a form was written with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OperandCount(usize);

impl From<usize> for OperandCount
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

impl From<OperandCount> for usize
{
    /// The number `count` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: OperandCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for OperandCount
{
    /// Writes the count in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// How many arguments a type head was written with.
///
/// The tables are indexed by this, so a head that answers at one arity and
/// not another is unresolved at the arity it was written with rather than
/// resolved and then rejected.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HeadArity
{
    /// The head was written bare, as `Integer`.
    Nullary,
    /// The head was written applied to one argument, as `+U C` or `Foo(A)`.
    Unary,
    /// The head was written applied to more than one argument, as `Foo(A, B)`.
    Polyadic(OperandCount),
}

impl fmt::Display for HeadArity
{
    /// Writes how the head was written.
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
            | Self::Nullary => f.write_str("bare"),
            | Self::Unary => f.write_str("applied to one argument"),
            | Self::Polyadic(count) => write!(f, "applied to {count} arguments"),
        }
    }
}

/// A nullary type head: a value-type atom of the fragment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeAtom
{
    /// `Unit`, the type inhabited by the unit value alone.
    Unit,
    /// `Integer`, the integer base atom.
    Integer,
    /// `String`, the text base atom.
    Text,
}

/// A unary type head: a type former of the fragment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeFormer
{
    /// `+U C`, the thunk of a computation type, which is a value type.
    Thunk,
    /// `-F A`, the returner over a value type, which is a computation type.
    Returner,
}

/// The nullary type heads, with the spellings the surface writes them as.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exact spelling selects the declared nullary type head; the other
///   arity and near spellings do not resolve.
/// - provides: one finite arity-indexed type-head inventory.
/// - executable: none — the specification attribute does not support constant
///   items; the lookup predicate checks the corresponding table.
///
/// # Adequacy
/// - hypothesis: L3 — every row has an exact answer, with the other arity and
///   near spellings separating the absent branch.
/// - witness: `resolve::tests::every_nullary_type_head_answers_its_atom`
/// - witness: `resolve::tests::a_near_miss_nullary_head_answers_nothing`
const TYPE_ATOMS: [(&str, TypeAtom); 3_usize] = [
    ("Unit", TypeAtom::Unit),
    ("Integer", TypeAtom::Integer),
    ("String", TypeAtom::Text),
];

/// The unary type heads, with the spellings the surface writes them as.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exact spelling selects the declared unary type head; the other
///   arity and near spellings do not resolve.
/// - provides: one finite arity-indexed type-head inventory.
/// - executable: none — the specification attribute does not support constant
///   items; the lookup predicate checks the corresponding table.
///
/// # Adequacy
/// - hypothesis: L3 — every row has an exact answer, with the other arity and
///   near spellings separating the absent branch.
/// - witness: `resolve::tests::every_unary_type_head_answers_its_former`
/// - witness: `resolve::tests::a_nullary_head_answers_no_former`
const TYPE_FORMERS: [(&str, TypeFormer); 2_usize] =
    [("+U", TypeFormer::Thunk), ("-F", TypeFormer::Returner)];

/// The value-type atom `name` spells, when the nullary table answers it.
///
/// # Specification
/// - requires: nothing — every identifier is admissible input.
/// - ensures: exactly the atom whose spelling equals `name`, and the absence
///   for every other identifier; the lookup is by the whole spelling, so a head
///   that merely starts with a table entry's text does not resolve.
/// - provides: the nullary half of the type-head resolution table.
/// - fails: never; an identifier the table does not hold is an absence, which
///   the caller reports as an unresolved head rather than as an opaque atom.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the table is a finite class, enumerated exhaustively with
///   each entry's exact answer asserted, and separated from the miss arm by a
///   proper prefix of an entry, an entry with a suffix, a case-shifted entry
///   and a former's spelling, each asserted absent; a dropped or swapped row
///   breaks one pair.
/// - witness: `resolve::tests::every_nullary_type_head_answers_its_atom`
/// - witness: `resolve::tests::a_near_miss_nullary_head_answers_nothing`
#[spec(
    ensures: |ret| match ret {
        | Maybe::Present(answer) => TYPE_ATOMS
            .iter()
            .any(|&(spelling, value)| spelling == name.as_ref() && value == answer),
        | Maybe::Absent(type_head::Absent::Unregistered) => TYPE_ATOMS
            .iter()
            .all(|&(spelling, _)| spelling != name.as_ref()),
    },
)]
#[inline]
pub fn type_atom(name: SurfaceName<'_>) -> Maybe<TypeAtom, type_head::Absent>
{
    let spelled: &str = name.as_ref();
    let found = TYPE_ATOMS
        .into_iter()
        .find_map(|(entry, atom)| (entry == spelled).then_some(atom));

    found.map_or(
        Maybe::Absent(type_head::Absent::Unregistered),
        Maybe::Present,
    )
}

/// The type former `name` spells, when the unary table answers it.
///
/// # Specification
/// - requires: nothing — every identifier is admissible input.
/// - ensures: exactly the former whose spelling equals `name`, and the absence
///   for every other identifier, a nullary atom's spelling included: `Unit`
///   applied to an argument is an unresolved head, not a former with the wrong
///   arity.
/// - provides: the unary half of the type-head resolution table.
/// - fails: never; an identifier the table does not hold is an absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the table is a finite class, enumerated exhaustively with
///   each entry's exact answer asserted, and separated from the miss arm by the
///   nullary heads' spellings and near misses of a former, each asserted
///   absent.
/// - witness: `resolve::tests::every_unary_type_head_answers_its_former`
/// - witness: `resolve::tests::a_nullary_head_answers_no_former`
#[spec(
    ensures: |ret| match ret {
        | Maybe::Present(answer) => TYPE_FORMERS
            .iter()
            .any(|&(spelling, value)| spelling == name.as_ref() && value == answer),
        | Maybe::Absent(type_head::Absent::Unregistered) => TYPE_FORMERS
            .iter()
            .all(|&(spelling, _)| spelling != name.as_ref()),
    },
)]
#[inline]
pub fn type_former(name: SurfaceName<'_>) -> Maybe<TypeFormer, type_head::Absent>
{
    let spelled: &str = name.as_ref();
    let found = TYPE_FORMERS
        .into_iter()
        .find_map(|(entry, former)| (entry == spelled).then_some(former));

    found.map_or(
        Maybe::Absent(type_head::Absent::Unregistered),
        Maybe::Present,
    )
}

/// The identity of one binder frame inside a [`Scope`].
///
/// # Specification
/// - requires: an interpreting scope accompanies the position.
/// - ensures: the coordinate names one frame only relative to that scope; it
///   does not authenticate where it was minted.
/// - provides: stable positions in an append-only binder arena.
/// - executable: none — a coordinate does not hold the arena needed to check
///   bounds or provenance.
///
/// # Adequacy
/// - hypothesis: L3 — sibling extensions preserve earlier positions; equal
///   positions from distinct scopes refer to the receiving scope's frames.
/// - witness: `resolve::tests::sibling_extensions_of_one_scope_are_independent`
/// - witness: `resolve::tests::binder_positions_do_not_authenticate_their_minting_scope`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(usize);

/// The binder frame a term is read under.
///
/// # Specification
/// - requires: an inner position is interpreted in its intended scope.
/// - ensures: outermost means no binder; an inner coordinate starts the parent
///   chain at that frame.
/// - provides: the binder context carried by a syntax node.
/// - executable: none — the frame holds no scope in which to establish its
///   bounds or parent chain.
///
/// # Adequacy
/// - hypothesis: L3 — outermost lookup is absent, while inner and sibling
///   chains resolve only their reachable binders.
/// - witness: `resolve::tests::an_unbound_name_resolves_to_nothing`
/// - witness: `resolve::tests::sibling_extensions_of_one_scope_are_independent`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Frame
{
    /// Under no binder: a declaration's own body, or an attribute payload.
    Outermost,
    /// Under the binder this frame names, and every binder it extends.
    Inner(ScopeId),
}

/// One binder, and the frame it extends.
///
/// # Specification
/// - requires: an arena position accompanies the frame.
/// - ensures: an inner parent precedes this frame; the stored name and optional
///   syntax type remain fixed while mention can change from false to true.
/// - provides: one persistent-chain node with mutable dependency evidence.
/// - executable: none — parent ordering needs the unheld arena position; push
///   and mention predicates check those transitions.
///
/// # Adequacy
/// - hypothesis: L3 — typed and untyped frames retain their data, and mention
///   affects telescope contribution without changing lexical lookup.
/// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
/// - witness: `resolve::tests::only_a_mentioned_typed_binder_counts_in_a_telescope`
#[derive(Clone, Copy, Debug)]
struct ScopeFrame<'source>
{
    /// The name this binder introduces.
    name: SurfaceName<'source>,
    /// The frame this one extends.
    parent: Frame,
    /// The type the binder was written with, as the syntax node holding it.
    declared: Maybe<NodeIndex, binder_type::Absent>,
    /// Whether a type position names this binder.
    mentioned: Mentioned,
}

/// Whether a type position names a binder, which makes a typed parameter's
/// arrow dependent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Mentioned(bool);

impl From<Mentioned> for bool
{
    /// Whether the binder is named by a type position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(mentioned: Mentioned) -> Self
    {
        mentioned.0
    }
}

/// A binder a name resolved to: its de Bruijn index at the use site, the
/// frame it introduced, and the type it was written with.
///
/// # Specification
/// - requires: the producing scope and use-site frame accompany the answer.
/// - ensures: index counts frames to the innermost matching binder, saturating
///   at the index width; its coordinate and written type are retained.
/// - provides: lexical resolution with enough data for dependent type decoding.
/// - executable: none — the answer holds neither the producing scope nor the
///   use-site chain; resolve checks their correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — inner shadowing and a typed outer binder have exact
///   indices, coordinates and optional syntax types.
/// - witness: `resolve::tests::an_inner_binder_shadows_an_outer_one`
/// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Bound
{
    /// The intervening binder count, saturating at the index width.
    pub index: DeBruijnIndex,
    /// The frame the binder introduced.
    pub binder: ScopeId,
    /// The syntax node of the binder's written type, when it has one.
    pub declared: Maybe<NodeIndex, binder_type::Absent>,
}

/// Every binder frame one lowering minted, as a persistent chain.
///
/// The chain is flat and id-addressed rather than pointer-linked: a frame names
/// its parent by position in this vector, so a scope is shared by every node
/// under one binder without being copied and without a drop that walks depth.
///
/// # Specification
/// - requires: extensions use an outermost parent or an existing frame position
///   in the intended scope.
/// - ensures: frames are append-only and parent links point backward;
///   independent sibling chains share prefixes without changing each other.
/// - provides: iterative lexical lookup and mention-filtered telescope indices.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; extension, lookup and mention predicates check the
///   boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — shadowing, sibling isolation, written types, mention
///   filtering and allowance exhaustion separate the observable transitions.
/// - witness: `resolve::tests::sibling_extensions_of_one_scope_are_independent`
/// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
/// - witness: `resolve::tests::lookup_spends_one_charge_per_visited_binder`
/// - witness: `resolve::tests::only_a_mentioned_typed_binder_counts_in_a_telescope`
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Scope<'source>
{
    /// The frames, in the order the binders were entered.
    frames: Vec<ScopeFrame<'source>>,
}

impl<'source> Scope<'source>
{
    /// A scope holding no binders.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self { frames: Vec::new() }
    }

    /// The frame that extends `parent` with an untyped binder for `name`.
    ///
    /// # Specification
    /// - requires: `parent` is outermost or an existing frame position in the
    ///   intended scope; a coordinate does not authenticate its minting scope.
    /// - ensures: the returned identity names a fresh frame whose parent is
    ///   `parent`, so the chain from it is one longer than the chain from
    ///   `parent`; existing frames are unchanged, which is what lets two
    ///   sibling subtrees hold different extensions of one scope at once.
    /// - provides: the binder half of term-name resolution.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one push and one parent link, separated by an
    ///   extension of the empty scope and an extension of a non-empty one, each
    ///   observed through the index the extended chain resolves the shadowed
    ///   and shadowing names at.
    /// - witness: `resolve::tests::an_inner_binder_shadows_an_outer_one`
    /// - witness: `resolve::tests::sibling_extensions_of_one_scope_are_independent`
    #[spec(
        requires: match parent {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        captures: before = self.frames.len(),
        ensures: |ret| {
            ret.0 == before
                && self.frames.len() == before.saturating_add(1)
                && self.frames.get(ret.0).is_some_and(|entry| {
                    entry.parent == parent
                        && entry.name == name
                        && entry.declared == Maybe::Absent(binder_type::Absent::Untyped)
                        && !entry.mentioned.0
                })
        },
    )]
    #[inline]
    pub fn extend(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
    ) -> ScopeId
    {
        self.push(parent, name, Maybe::Absent(binder_type::Absent::Untyped))
    }

    /// The frame that extends `parent` with a binder for `name` written with
    /// the type at `declared`.
    ///
    /// # Specification
    /// - requires: as [`Self::extend`]; `declared` is the syntax node of the
    ///   binder's written type.
    /// - ensures: as [`Self::extend`], and a name resolving to the new binder
    ///   answers `declared` beside its index.
    /// - provides: the typed binder of a function tail's parameter list, whose
    ///   written universe a decode reads its sort and level from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed and an untyped binder in one chain, each
    ///   resolved and its written type asserted present and absent.
    /// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
    #[spec(
        requires: match parent {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        captures: before = self.frames.len(),
        ensures: |ret| {
            ret.0 == before
                && self.frames.len() == before.saturating_add(1)
                && self.frames.get(ret.0).is_some_and(|entry| {
                    entry.parent == parent
                        && entry.name == name
                        && entry.declared == Maybe::Present(declared)
                        && !entry.mentioned.0
                })
        },
    )]
    #[inline]
    pub fn extend_typed(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
        declared: NodeIndex,
    ) -> ScopeId
    {
        self.push(parent, name, Maybe::Present(declared))
    }

    /// Push one binder frame over `parent`.
    ///
    /// # Specification
    /// - requires: parent is outermost or names an existing frame position.
    /// - ensures: the new last frame retains parent, name and written type,
    ///   starts unmentioned and leaves earlier frame positions intact.
    /// - provides: the append boundary shared by typed and untyped extension.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — siblings stay independent, shadowing stops at the
    ///   innermost binder and typed versus untyped results retain their written
    ///   type.
    /// - witness: `resolve::tests::sibling_extensions_of_one_scope_are_independent`
    /// - witness: `resolve::tests::an_inner_binder_shadows_an_outer_one`
    /// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
    #[spec(
        requires: match parent {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        captures: before = self.frames.len(),
        ensures: |ret| {
            ret.0 == before
                && self.frames.len() == before.saturating_add(1)
                && self.frames.get(ret.0).is_some_and(|entry| {
                    entry.parent == parent
                        && entry.name == name
                        && entry.declared == declared
                        && !entry.mentioned.0
                })
        },
    )]
    fn push(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
        declared: Maybe<NodeIndex, binder_type::Absent>,
    ) -> ScopeId
    {
        let minted = ScopeId(self.frames.len());
        self.frames.push(ScopeFrame {
            name,
            parent,
            declared,
            mentioned: Mentioned(false),
        });

        minted
    }

    /// The de Bruijn index `name` has in the chain rooted at `frame`.
    ///
    /// # Specification
    /// - requires: as [`Self::resolve`].
    /// - ensures: the index [`Self::resolve`] answers, without the binder's
    ///   written type.
    /// - provides: the binder half of term-name resolution.
    /// - fails: as [`Self::resolve`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out
    /// mid-walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three decision surfaces (the name comparison, the
    ///   depth step, the allowance check) separated by a hit at the innermost
    ///   binder, a hit one binder out, a shadowed outer binder of the same
    ///   name, a miss over a non-empty chain, and an allowance exhausted
    ///   mid-walk, each asserted as an exact index or an exact refusal variant.
    /// - witness: `resolve::tests::the_innermost_binder_resolves_at_index_zero`
    /// - witness: `resolve::tests::an_outer_binder_resolves_one_index_further`
    /// - witness: `resolve::tests::an_inner_binder_shadows_an_outer_one`
    /// - witness: `resolve::tests::an_unbound_name_resolves_to_nothing`
    /// - witness: `resolve::tests::a_chain_walk_past_the_allowance_is_refused`
    #[spec(
        requires: match frame {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        ensures: |ret| match ret {
            | Ok(Maybe::Present(index)) => {
                usize::try_from(u32::from(index)).is_ok_and(|depth| depth < self.frames.len())
            },
            | Ok(Maybe::Absent(binder::Absent::Unbound)) => true,
            | Err(LoweringRefusal::BudgetExceeded { .. }) => matches!(frame, Frame::Inner(_)),
            | Err(_) => false,
        },
    )]
    #[inline]
    pub fn index_of<'refusal>(
        &self,
        frame: Frame,
        name: SurfaceName<'_>,
        fuel: &mut Fuel,
    ) -> Result<Maybe<DeBruijnIndex, binder::Absent>, LoweringRefusal<'refusal>>
    {
        Ok(self.resolve(frame, name, fuel)?.map(|bound| bound.index))
    }

    /// The binder `name` resolves to in the chain rooted at `frame`.
    ///
    /// # Specification
    /// - requires: `frame` is outermost or an existing frame position in the
    ///   intended scope; `fuel` holds the remaining allowance.
    /// - ensures: on a hit, the number of binders strictly between the use site
    ///   and the innermost binder of `name` — zero at the innermost binder, so
    ///   an inner binder shadows an outer one of the same name — with the type
    ///   that binder was written with; the unbound absence when no binder in
    ///   the chain carries the name.
    /// - provides: the only place a surface name becomes a de Bruijn index.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the chain walk outruns
    ///   the lowering's allowance, which is what bounds an otherwise quadratic
    ///   walk over a deep binder chain.
    /// - panics: none. Depth conversion saturates at the index width; the
    ///   caller-selected allowance is not itself limited to that width.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out
    /// mid-walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::index_of`], whose witnesses walk this
    ///   chain, and the written type separated by a typed and an untyped
    ///   binder.
    /// - witness: `resolve::tests::an_outer_binder_resolves_one_index_further`
    /// - witness: `resolve::tests::a_chain_walk_past_the_allowance_is_refused`
    /// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
    /// - witness: `resolve::tests::lookup_spends_one_charge_per_visited_binder`
    #[spec(
        requires: match frame {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        ensures: |ret| match ret {
            | Ok(answer) => {
                let mut current = frame;
                let mut depth = 0_usize;
                let expected = loop {
                    let Frame::Inner(id) = current
                    else {
                        break Maybe::Absent(binder::Absent::Unbound);
                    };
                    if depth >= self.frames.len() {
                        return false;
                    }
                    let Some(entry) = self.frames.get(id.0)
                    else {
                        return false;
                    };
                    if entry.name == name {
                        break Maybe::Present(Bound {
                            index: DeBruijnIndex::from(u32::try_from(depth).unwrap_or(u32::MAX)),
                            binder: id,
                            declared: entry.declared,
                        });
                    }
                    depth = depth.saturating_add(1);
                    current = entry.parent;
                };
                answer == expected
            },
            | Err(LoweringRefusal::BudgetExceeded { .. }) => matches!(frame, Frame::Inner(_)),
            | Err(_) => false,
        },
    )]
    #[inline]
    pub fn resolve<'refusal>(
        &self,
        frame: Frame,
        name: SurfaceName<'_>,
        fuel: &mut Fuel,
    ) -> Result<Maybe<Bound, binder::Absent>, LoweringRefusal<'refusal>>
    {
        let spelled: &str = name.as_ref();
        let mut current = frame;
        let mut depth = 0_usize;
        while let Frame::Inner(ScopeId(position)) = current {
            fuel.spend()?;
            let Some(entry) = self.frames.get(position)
            else {
                break;
            };
            if entry.name.as_ref() == spelled {
                let index = u32::try_from(depth).unwrap_or(u32::MAX);

                return Ok(Maybe::Present(Bound {
                    index: DeBruijnIndex::from(index),
                    binder: ScopeId(position),
                    declared: entry.declared,
                }));
            }
            depth = depth.saturating_add(1_usize);
            current = entry.parent;
        }

        Ok(Maybe::Absent(binder::Absent::Unbound))
    }

    /// Record that a type position names the binder that introduced `binder`.
    ///
    /// # Specification
    /// - requires: nothing — the coordinate is interpreted in this scope.
    /// - ensures: a stored frame is mentioned from now on; every other frame is
    ///   unchanged. Equal coordinates from other scopes name this scope's
    ///   frame, not their original owner.
    /// - provides: the half of the dependent-arrow decision a type position
    ///   contributes.
    /// - fails: never; an out-of-range coordinate is ignored.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mentioned and an unmentioned typed binder in one
    ///   chain, separated by the flag and by the telescope index they leave.
    /// - witness: `resolve::tests::only_a_mentioned_typed_binder_counts_in_a_telescope`
    /// - witness: `resolve::tests::binder_positions_do_not_authenticate_their_minting_scope`
    #[spec(
        captures: before = self.frames.len(),
        ensures: self.frames.len() == before
            && self
                .frames
                .get(binder.0)
                .is_none_or(|entry| entry.mentioned.0),
    )]
    #[inline]
    pub fn mention(
        &mut self,
        binder: ScopeId,
    )
    {
        if let Some(entry) = self.frames.get_mut(binder.0) {
            entry.mentioned = Mentioned(true);
        }
    }

    /// Whether a type position names the binder that introduced `binder`.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range coordinate is admissible.
    /// - ensures: a stored frame answers its mention flag; an out-of-range
    ///   coordinate answers false.
    /// - provides: the dependency decision without mutating lexical resolution.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mentioned, unmentioned, aliased and out-of-range
    ///   coordinates distinguish the receiving arena's local flag from
    ///   provenance.
    /// - witness: `resolve::tests::only_a_mentioned_typed_binder_counts_in_a_telescope`
    /// - witness: `resolve::tests::binder_positions_do_not_authenticate_their_minting_scope`
    #[spec(
        ensures: |ret| {
            ret.0
                == self
                    .frames
                    .get(binder.0)
                    .is_some_and(|entry| entry.mentioned.0)
        },
    )]
    #[inline]
    #[must_use]
    pub fn mentioned(
        &self,
        binder: ScopeId,
    ) -> Mentioned
    {
        self.frames
            .get(binder.0)
            .map_or(Mentioned(false), |entry| entry.mentioned)
    }

    /// The de Bruijn index the binder `binder` has from `from` in a telescope:
    /// the binders strictly between, counting a typed binder only when a type
    /// position names it.
    ///
    /// # Specification
    /// - requires: `from` is outermost or an existing frame position in the
    ///   intended scope; every mention has been recorded.
    /// - ensures: counts from `from` up to but excluding `binder`, including
    ///   each untyped or mentioned frame. If the target is not on the chain,
    ///   counts to its end; an unmentioned typed frame contributes nothing. The
    ///   count saturates at the index width.
    /// - provides: the index a decode in a function tail's signature carries.
    /// - fails: never; a chain that never reaches `binder` counts to its end.
    /// - panics: none. The walk follows parent links, which always name an
    ///   earlier frame, so it ends.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mentioned typed binder, an unmentioned one and an
    ///   untyped one between the use site and the binder, each asserted to
    ///   count or not.
    /// - witness: `resolve::tests::only_a_mentioned_typed_binder_counts_in_a_telescope`
    /// - witness: `resolve::tests::telescope_counts_to_the_end_when_the_target_is_not_on_the_chain`
    #[spec(
        requires: match from {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        ensures: |ret| {
            let mut current = from;
            let mut count = 0_u32;
            let mut visited = 0_usize;
            while let Frame::Inner(id) = current {
                if id == binder {
                    break;
                }
                if visited >= self.frames.len() {
                    return false;
                }
                let Some(entry) = self.frames.get(id.0)
                else {
                    return false;
                };
                if matches!(entry.declared, Maybe::Absent(_)) || entry.mentioned.0 {
                    count = count.saturating_add(1);
                }
                visited = visited.saturating_add(1);
                current = entry.parent;
            }
            u32::from(ret) == count
        },
    )]
    #[inline]
    #[must_use]
    pub fn telescope_index(
        &self,
        from: Frame,
        binder: ScopeId,
    ) -> DeBruijnIndex
    {
        let mut current = from;
        let mut depth = 0_u32;
        while let Frame::Inner(here) = current
            && here != binder
        {
            let Some(entry) = self.frames.get(here.0)
            else {
                break;
            };
            let binds = match entry.declared {
                | Maybe::Present(_) => entry.mentioned.0,
                | Maybe::Absent(_) => true,
            };
            if binds {
                depth = depth.saturating_add(1_u32);
            }
            current = entry.parent;
        }

        DeBruijnIndex::from(depth)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_surface_syntax::NodeIndex;
    use quenchant_shape::shape::Maybe;

    use super::Bound;
    use super::Frame;
    use super::Scope;
    use super::SurfaceName;
    use super::TypeAtom;
    use super::TypeFormer;
    use super::binder;
    use super::binder_type;
    use super::type_atom;
    use super::type_former;
    use super::type_head;
    use crate::error::LoweringRefusal;
    use crate::lower::Fuel;
    use crate::lower::LoweringBudget;

    /// A tank with room for eight charges, which every fixture here fits in.
    ///
    /// # Specification
    /// trivial.
    fn tank() -> Fuel
    {
        Fuel::new(LoweringBudget::from(8_usize))
    }

    #[test]
    fn binder_positions_do_not_authenticate_their_minting_scope()
    {
        let mut first = Scope::new();
        let foreign = first.extend(Frame::Outermost, SurfaceName::from("foreign"));
        let outside = first.extend(Frame::Inner(foreign), SurfaceName::from("outside"));
        let mut receiving = Scope::new();
        let local = receiving.extend(Frame::Outermost, SurfaceName::from("local"));
        assert_eq!(foreign, local);
        receiving.mention(outside);
        assert!(!bool::from(receiving.mentioned(outside)));
        assert!(!bool::from(receiving.mentioned(local)));
        receiving.mention(foreign);
        assert!(bool::from(receiving.mentioned(local)));
        assert!(!bool::from(first.mentioned(foreign)));
        assert_eq!(
            receiving.index_of(
                Frame::Inner(foreign),
                SurfaceName::from("local"),
                &mut tank()
            ),
            Ok(Maybe::Present(DeBruijnIndex::from(0_u32)))
        );
        assert_eq!(
            receiving.index_of(
                Frame::Inner(foreign),
                SurfaceName::from("foreign"),
                &mut tank()
            ),
            Ok(Maybe::Absent(binder::Absent::Unbound))
        );
    }

    #[test]
    fn lookup_spends_one_charge_per_visited_binder()
    {
        let mut scope = Scope::new();
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"));
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("y"));
        let cases = [
            (
                Frame::Outermost,
                "x",
                0_usize,
                Ok(Maybe::Absent(binder::Absent::Unbound)),
            ),
            (
                Frame::Inner(inner),
                "y",
                1_usize,
                Ok(Maybe::Present(DeBruijnIndex::from(0_u32))),
            ),
            (
                Frame::Inner(inner),
                "x",
                2_usize,
                Ok(Maybe::Present(DeBruijnIndex::from(1_u32))),
            ),
            (
                Frame::Inner(outer),
                "missing",
                1_usize,
                Ok(Maybe::Absent(binder::Absent::Unbound)),
            ),
            (
                Frame::Inner(inner),
                "y",
                0_usize,
                Err(LoweringRefusal::BudgetExceeded {
                    budget: LoweringBudget::from(0_usize),
                }),
            ),
        ];
        for (frame, name, allowance, expected) in cases {
            let budget = LoweringBudget::from(allowance);
            let mut fuel = Fuel::new(budget);
            assert_eq!(
                scope.index_of(frame, SurfaceName::from(name), &mut fuel),
                expected
            );
            assert_eq!(
                fuel.spend(),
                Err(LoweringRefusal::BudgetExceeded { budget })
            );
        }
        let budget = LoweringBudget::from(1_usize);
        let mut fuel = Fuel::new(budget);
        assert_eq!(
            scope.index_of(Frame::Outermost, SurfaceName::from("x"), &mut fuel),
            Ok(Maybe::Absent(binder::Absent::Unbound))
        );
        assert_eq!(fuel.spend(), Ok(()));
        assert_eq!(
            fuel.spend(),
            Err(LoweringRefusal::BudgetExceeded { budget })
        );
    }

    #[test]
    fn telescope_counts_to_the_end_when_the_target_is_not_on_the_chain()
    {
        let mut scope = Scope::new();
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("outer"));
        let typed = scope.extend_typed(
            Frame::Inner(outer),
            SurfaceName::from("typed"),
            NodeIndex::from(7_usize),
        );
        let inner = scope.extend(Frame::Inner(typed), SurfaceName::from("inner"));
        let sibling = scope.extend(Frame::Outermost, SurfaceName::from("sibling"));
        assert_eq!(
            scope.telescope_index(Frame::Inner(inner), sibling),
            DeBruijnIndex::from(2_u32)
        );
        scope.mention(typed);
        assert_eq!(
            scope.telescope_index(Frame::Inner(inner), sibling),
            DeBruijnIndex::from(3_u32)
        );
        assert_eq!(
            scope.telescope_index(Frame::Inner(inner), inner),
            DeBruijnIndex::from(0_u32)
        );
        assert_eq!(
            scope.telescope_index(Frame::Outermost, sibling),
            DeBruijnIndex::from(0_u32)
        );
    }
    #[test]
    fn every_nullary_type_head_answers_its_atom()
    {
        let expected = [
            ("Unit", TypeAtom::Unit),
            ("Integer", TypeAtom::Integer),
            ("String", TypeAtom::Text),
        ];

        for (spelling, atom) in expected {
            assert_eq!(
                type_atom(SurfaceName::from(spelling)),
                Maybe::Present(atom),
                "the nullary table is pinned row by row"
            );
        }
    }

    #[test]
    fn a_near_miss_nullary_head_answers_nothing()
    {
        for spelling in ["Integ", "Integers", "integer", "+U", ""] {
            assert_eq!(
                type_atom(SurfaceName::from(spelling)),
                Maybe::Absent(type_head::Absent::Unregistered),
                "the lookup matches the whole spelling and nothing near it"
            );
        }
    }

    #[test]
    fn every_unary_type_head_answers_its_former()
    {
        let expected = [("+U", TypeFormer::Thunk), ("-F", TypeFormer::Returner)];

        for (spelling, former) in expected {
            assert_eq!(
                type_former(SurfaceName::from(spelling)),
                Maybe::Present(former),
                "the unary table is pinned row by row"
            );
        }
    }

    #[test]
    fn a_nullary_head_answers_no_former()
    {
        for spelling in ["Unit", "Integer", "String", "Uu", "f"] {
            assert_eq!(
                type_former(SurfaceName::from(spelling)),
                Maybe::Absent(type_head::Absent::Unregistered),
                "an atom applied to an argument is an unresolved head, not a former"
            );
        }
    }

    #[test]
    fn the_innermost_binder_resolves_at_index_zero()
    {
        let mut scope = Scope::new();
        let inner = scope.extend(Frame::Outermost, SurfaceName::from("x"));

        assert_eq!(
            scope.index_of(Frame::Inner(inner), SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Present(DeBruijnIndex::from(0_u32))),
            "the binder at the use site counts zero binders out"
        );
    }

    #[test]
    fn an_outer_binder_resolves_one_index_further()
    {
        let mut scope = Scope::new();
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"));
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("y"));

        assert_eq!(
            scope.index_of(Frame::Inner(inner), SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Present(DeBruijnIndex::from(1_u32))),
            "one intervening binder is one index"
        );
        assert_eq!(
            scope.index_of(Frame::Inner(inner), SurfaceName::from("y"), &mut tank()),
            Ok(Maybe::Present(DeBruijnIndex::from(0_u32))),
            "the innermost binder still counts zero"
        );
    }

    #[test]
    fn an_inner_binder_shadows_an_outer_one()
    {
        let mut scope = Scope::new();
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"));
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("x"));

        assert_eq!(
            scope.index_of(Frame::Inner(inner), SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Present(DeBruijnIndex::from(0_u32))),
            "the walk stops at the first binder carrying the name"
        );
        assert_eq!(
            scope.index_of(Frame::Inner(outer), SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Present(DeBruijnIndex::from(0_u32))),
            "the outer frame is unchanged by the extension"
        );
    }

    #[test]
    fn sibling_extensions_of_one_scope_are_independent()
    {
        let mut scope = Scope::new();
        let shared = scope.extend(Frame::Outermost, SurfaceName::from("x"));
        let left = scope.extend(Frame::Inner(shared), SurfaceName::from("y"));
        let right = scope.extend(Frame::Inner(shared), SurfaceName::from("z"));

        assert_eq!(
            scope.index_of(Frame::Inner(left), SurfaceName::from("z"), &mut tank()),
            Ok(Maybe::Absent(binder::Absent::Unbound)),
            "one sibling's binder is invisible to the other"
        );
        assert_eq!(
            scope.index_of(Frame::Inner(right), SurfaceName::from("z"), &mut tank()),
            Ok(Maybe::Present(DeBruijnIndex::from(0_u32))),
            "each sibling sees its own binder at the innermost index"
        );
    }

    #[test]
    fn an_unbound_name_resolves_to_nothing()
    {
        let mut scope = Scope::new();
        let frame = scope.extend(Frame::Outermost, SurfaceName::from("x"));

        assert_eq!(
            scope.index_of(Frame::Inner(frame), SurfaceName::from("y"), &mut tank()),
            Ok(Maybe::Absent(binder::Absent::Unbound)),
            "a name no binder carries leaves the binder scope unanswered"
        );
        assert_eq!(
            scope.index_of(Frame::Outermost, SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Absent(binder::Absent::Unbound)),
            "the empty chain answers nothing at all"
        );
    }

    #[test]
    fn a_chain_walk_past_the_allowance_is_refused()
    {
        let mut scope = Scope::new();
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"));
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("y"));
        let budget = LoweringBudget::from(1_usize);

        assert_eq!(
            scope.index_of(
                Frame::Inner(inner),
                SurfaceName::from("x"),
                &mut Fuel::new(budget)
            ),
            Err(LoweringRefusal::BudgetExceeded { budget }),
            "a walk longer than the allowance is an engine fault, not a miss"
        );
    }

    #[test]
    fn a_typed_binder_resolves_with_its_written_type()
    {
        let mut scope = Scope::new();
        let typed = scope.extend_typed(
            Frame::Outermost,
            SurfaceName::from("a"),
            NodeIndex::from(7_usize),
        );
        let untyped = scope.extend(Frame::Inner(typed), SurfaceName::from("x"));

        assert_eq!(
            scope.resolve(Frame::Inner(untyped), SurfaceName::from("a"), &mut tank()),
            Ok(Maybe::Present(Bound {
                index: DeBruijnIndex::from(1_u32),
                binder: typed,
                declared: Maybe::Present(NodeIndex::from(7_usize)),
            })),
            "a typed binder answers the node its type was written at"
        );
        assert_eq!(
            scope.resolve(Frame::Inner(untyped), SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Present(Bound {
                index: DeBruijnIndex::from(0_u32),
                binder: untyped,
                declared: Maybe::Absent(binder_type::Absent::Untyped),
            })),
            "an untyped binder answers no written type"
        );
    }

    #[test]
    fn only_a_mentioned_typed_binder_counts_in_a_telescope()
    {
        let mut scope = Scope::new();
        let typed = |scope: &mut Scope<'static>, parent: Frame, name: &'static str| {
            scope.extend_typed(parent, SurfaceName::from(name), NodeIndex::from(1_usize))
        };
        let a = typed(&mut scope, Frame::Outermost, "a");
        let b = typed(&mut scope, Frame::Inner(a), "b");
        let x = typed(&mut scope, Frame::Inner(b), "x");
        let y = scope.extend(Frame::Inner(x), SurfaceName::from("y"));
        scope.mention(a);
        scope.mention(b);

        assert!(
            bool::from(scope.mentioned(b)) && !bool::from(scope.mentioned(x)),
            "the flag is set on the mentioned binder alone"
        );
        assert_eq!(
            scope.telescope_index(Frame::Inner(x), a),
            DeBruijnIndex::from(1_u32),
            "a mentioned typed binder between counts"
        );
        assert_eq!(
            scope.telescope_index(Frame::Inner(x), b),
            DeBruijnIndex::from(0_u32),
            "an unmentioned typed binder between counts nothing"
        );
        assert_eq!(
            scope.telescope_index(Frame::Inner(y), b),
            DeBruijnIndex::from(1_u32),
            "an untyped binder between always counts"
        );
    }
}
