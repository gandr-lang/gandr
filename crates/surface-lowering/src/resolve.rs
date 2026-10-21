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
//! atom former reachable from name resolution. The unit value is the keyword
//! `unit`, a form of its own, so no name answers it.
//!
//! # Names resolve through tables with no fallthrough
//!
//! A type head answers first from the binders enclosing it and the declarations
//! strictly earlier in admission order, as a term name does — a value name in
//! type position is a code, and decodes (the `lower` module's § Five
//! insertions, by the sort of the position) — and then from a table indexed by
//! how it was written: bare, `Unit`, `Integer` and `String`; applied to one
//! argument, `+U` and `-F`. `Type` is its own former, not a table entry. A head
//! a binder or a declaration answers is answered there at every arity: applied
//! to arguments it is a static application (the `lower` module's § Type
//! operators are static functions over codes), and the table is never
//! consulted. A head nothing answers is `UnresolvedTypeHead` carrying the arity
//! it was written with, and a head applied to several arguments reports how
//! many. Since the bridges are the compound tokens `+U` and `-F`, `U` and `F`
//! alone are ordinary names that nothing declares. A term name answers from the
//! binders enclosing it, innermost first, and then from the declarations
//! strictly earlier in admission order; nothing answers otherwise. A
//! capitalised name in term position answers the same way, and when nothing
//! does, a type atom or `Type` stands as a type and is quoted; any other is a
//! constructor, which the fragment does not admit. The unit value is the
//! keyword `unit` and its type `Unit`; the empty parentheses `()` are an empty
//! list, refused as a value or a type (`EmptyList`), and read only before `=>`,
//! where `() => C` takes no argument and is `+U (-F C)`, distinct from `Unit =>
//! C`. The `unit` pattern is the empty product's, `#{}` spelled as the value
//! it matches: a match splits its scrutinee into no components.
//!
//! Choice: the unit value is a keyword, and `()` is never the unit. A product
//! of no components and a domain list of no members are both the empty list, so
//! reading `()` as the unit would make `() => C` and `Unit => C` the same type
//! and give the n-ary product `#{}` two spellings of its nullary case.
//! Alternatives: `()` as the unit, which conflates the empty domain list with
//! the one-argument function over `Unit`; and a primitive term table answering
//! the name `unit`, which a declaration could shadow. Reversal: none while
//! `#{}` spells the nullary product.
//!
//! Binder predicates check backward parent links, fresh frame positions, exact
//! successful lookup and mention-filtered telescope counts. `ScopeId` is a
//! scope-relative coordinate, not an ownership certificate: an equal coordinate
//! from another scope addresses the receiving scope's frame, while an
//! out-of-range mention is ignored. Lookup spends one charge per visited binder
//! and none at the outermost frame. Telescope lookup counts from the use frame
//! up to the target, excluding the target, or to the chain's end when the
//! target is absent. Index conversion saturates at the index width; the
//! caller-selected allowance is not limited to that width.
//!
//! Witness for the nullary table:
//! `tests::every_nullary_type_head_answers_its_atom`.
//!
//! # A frame keeps where its binder was written
//!
//! Each frame a written binder enters keeps the binder's span; a frame the
//! lowering enters for a value the source names nothing — a discarded
//! statement's, a split's tuple, a positional parameter's — keeps none. A
//! variable the lowering mints reads its binder's span here and records it in
//! the origin table, so a face goes from a use to its binder without a second
//! resolution. The alternative was a side table of binder spans in the
//! lowerer, keyed by frame, which is a second copy of the frame's identity;
//! the frame is where the binder already lives. Witness:
//! `tests::a_frame_keeps_its_binder_s_span`.
//!
//! # A linear binder counts apart
//!
//! A fork's two ends bind into the core's linear zone, whose indices count
//! linear binders only, while every other binder binds into the
//! intuitionistic zone and counts intuitionistic binders only. One chain
//! holds both, each frame tagged with its zone, so shadowing and lookup stay
//! one walk: a name resolves to its innermost binder of either zone, and its
//! index counts the frames of that binder's zone between the use and the
//! binder. A telescope never binds linearly, so its counts pass linear frames
//! by. The alternative was a second chain for endpoints, which duplicates
//! shadowing between the two; the reversal is a core context whose zones
//! share one index space. Witness:
//! `tests::a_linear_binder_counts_apart_from_intuitionistic_ones`.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
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
            /// A lambda's binder, a statement's, a pattern's field, or a
            /// parameter written untyped.
            Untyped,
            /// A static lambda's binder: an operand of a type operator,
            /// which an application of it applies statically.
            Operand,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a binder frame keeps no span.
    pub mod binder_site {
        /// The frame binds a value the source names nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A discarded statement's result, the tuple a split takes apart,
            /// or a positional parameter, which no name in the source binds.
            Unwritten,
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
            Self::Nullary => f.write_str("bare"),
            Self::Unary => f.write_str("applied to one argument"),
            Self::Polyadic(count) => write!(f, "applied to {count} arguments"),
        }
    }
}

/// A nullary type head: a value-type atom of the fragment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeAtom
{
    /// `Bool`, the canonical sum of two unit types.
    Boolean,
    /// `Unit`, the type inhabited by the unit value alone.
    Unit,
    /// `Integer`, the integer base atom.
    Integer,
    /// `String`, the text base atom.
    Text,
    /// `Void`, the sum of no summands, eliminated by a case of no arms.
    Void,
}

/// A unary type head: a type former of the fragment.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeFormer
{
    /// `+U C`, the thunk of a computation type, which is a value type.
    Thunk,
    /// `-F A`, the returner over a value type, which is a computation type.
    Returner,
    /// `List(A)`, the native finite lists over a value type.
    List,
    /// `Run(S)`, the value type of the complete recorded runs of the session
    /// code `S`, which is read as a value.
    Run,
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
/// - witness: `lower::tests::native_boolean_results_have_the_written_classifier`
/// - witness: `resolve::tests::a_near_miss_nullary_head_answers_nothing`
const TYPE_ATOMS: [(&str, TypeAtom); 5_usize] = [
    ("Unit", TypeAtom::Unit),
    ("Void", TypeAtom::Void),
    ("Bool", TypeAtom::Boolean),
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
const TYPE_FORMERS: [(&str, TypeFormer); 4_usize] = [
    ("+U", TypeFormer::Thunk),
    ("-F", TypeFormer::Returner),
    ("List", TypeFormer::List),
    ("Run", TypeFormer::Run),
];

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
/// - hypothesis: L3 — source signatures select their concrete classifiers; near
///   spellings and a former's spelling remain absent.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::native_boolean_results_have_the_written_classifier`
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
    /// Whether a signature's type position names this binder.
    mentioned: Mentioned,
    /// Whether a type quoted in a body names this binder.
    quoted: Mentioned,
    /// Where the binder was written, when the source names it.
    site: Maybe<ByteSpan, binder_site::Absent>,
    /// The zone the binder binds into.
    zone: Zone,
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

/// The telescope a type counts its binders in: a typed binder binds in the
/// signature's once a signature type names it, and in a body quote's once a
/// signature type or a body quote names it (#547).
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Telescope
{
    /// The signature's telescope, whose binders make arrows dependent.
    Signature,
    /// A type quoted in a body, carried into the body's context once minted.
    Quote,
}

impl ScopeFrame<'_>
{
    /// Whether this frame binds in `telescope`: never a linear frame, always
    /// an untyped one, and a typed one once a type of that telescope names it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn binds_in(
        &self,
        telescope: Telescope,
    ) -> Mentioned
    {
        Mentioned(match (self.zone, self.declared, telescope) {
            (Zone::Linear, ..) => false,
            (_, Maybe::Absent(_), _) => true,
            (_, Maybe::Present(_), Telescope::Signature) => self.mentioned.0,
            (_, Maybe::Present(_), Telescope::Quote) => self.mentioned.0 || self.quoted.0,
        })
    }
}

/// A binder a name resolved to: its de Bruijn index at the use site, the
/// frame it introduced, the type it was written with and its zone.
///
/// # Specification
/// - requires: the producing scope and use-site frame accompany the answer.
/// - ensures: index counts the frames of the binder's zone strictly between the
///   use and the innermost matching binder, saturating at the index width; its
///   coordinate, written type and zone are retained.
/// - provides: lexical resolution with enough data for dependent type decoding.
/// - executable: none — the answer holds neither the producing scope nor the
///   use-site chain; resolve checks their correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — inner shadowing and a typed outer binder have exact
///   indices, coordinates and optional syntax types.
/// - witness: `resolve::tests::an_inner_binder_shadows_an_outer_one`
/// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
/// - witness: `resolve::tests::a_linear_binder_counts_apart_from_intuitionistic_ones`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Bound
{
    /// The intervening binder count, saturating at the index width.
    pub index: DeBruijnIndex,
    /// The frame the binder introduced.
    pub binder: ScopeId,
    /// The syntax node of the binder's written type, when it has one.
    pub declared: Maybe<NodeIndex, binder_type::Absent>,
    /// The zone the binder binds into, which the index counts within.
    pub zone: Zone,
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

    /// The frame that extends `parent` with an untyped binder for `name`,
    /// written at `site`.
    ///
    /// # Specification
    /// - requires: `parent` is outermost or an existing frame position in the
    ///   intended scope; a coordinate does not authenticate its minting scope.
    /// - ensures: the returned identity names a fresh frame whose parent is
    ///   `parent`, so the chain from it is one longer than the chain from
    ///   `parent`, and which keeps `site`; existing frames are unchanged, which
    ///   is what lets two sibling subtrees hold different extensions of one
    ///   scope at once.
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
                        && entry.site == site
                        && !entry.mentioned.0
                })
        },
    )]
    #[inline]
    pub fn extend(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
        site: Maybe<ByteSpan, binder_site::Absent>,
    ) -> ScopeId
    {
        self.push(
            parent,
            name,
            Maybe::Absent(binder_type::Absent::Untyped),
            site,
            Zone::Intuitionistic,
        )
    }

    /// The frame that extends `parent` with a static lambda's binder for
    /// `name` written at `site`.
    ///
    /// # Specification
    /// - requires: as [`Self::extend`].
    /// - ensures: as [`Self::extend`], the new binder answering the operand
    ///   absence for its written type.
    /// - provides: the binder of a type operator's operand, whose application
    ///   is static where a dynamic function's would be a call.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an operator's binder applied where a computation type
    ///   is read decodes its static application rather than a call's return.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        requires: match parent {
            | Frame::Outermost => true,
            | Frame::Inner(id) => id.0 < self.frames.len(),
        },
        captures: before = self.frames.len(),
        ensures: |ret| {
            ret.0 == before
                && self.frames.get(ret.0).is_some_and(|entry| {
                    entry.parent == parent
                        && entry.declared == Maybe::Absent(binder_type::Absent::Operand)
                })
        },
    )]
    #[inline]
    pub fn extend_operand(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
        site: Maybe<ByteSpan, binder_site::Absent>,
    ) -> ScopeId
    {
        self.push(
            parent,
            name,
            Maybe::Absent(binder_type::Absent::Operand),
            site,
            Zone::Intuitionistic,
        )
    }

    /// The frame that extends `parent` with a binder for `name` written at
    /// `site` with the type at `declared`.
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
                        && entry.site == site
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
        site: Maybe<ByteSpan, binder_site::Absent>,
    ) -> ScopeId
    {
        self.push(
            parent,
            name,
            Maybe::Present(declared),
            site,
            Zone::Intuitionistic,
        )
    }

    /// The frame that extends `parent` with a linear binder for `name`,
    /// written at `site`: one end of a fork.
    ///
    /// # Specification
    /// - requires: as [`Self::extend`].
    /// - ensures: as [`Self::extend`], the new frame in the linear zone, so a
    ///   name resolving to it counts only the linear frames between.
    /// - provides: the endpoint binder of a fork's child and of the rest of its
    ///   block.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a linear binder under and over intuitionistic ones,
    ///   each resolved at its own zone's index.
    /// - witness: `resolve::tests::a_linear_binder_counts_apart_from_intuitionistic_ones`
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
                        && entry.site == site
                        && entry.zone == Zone::Linear
                })
        },
    )]
    #[inline]
    pub fn extend_linear(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
        site: Maybe<ByteSpan, binder_site::Absent>,
    ) -> ScopeId
    {
        self.push(
            parent,
            name,
            Maybe::Absent(binder_type::Absent::Untyped),
            site,
            Zone::Linear,
        )
    }

    /// Push one binder frame over `parent`.
    ///
    /// # Specification
    /// - requires: parent is outermost or names an existing frame position.
    /// - ensures: the new last frame retains parent, name, written type, site
    ///   and zone, starts unmentioned and leaves earlier frame positions
    ///   intact.
    /// - provides: the append boundary shared by typed, untyped and linear
    ///   extension.
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
                        && entry.site == site
                        && !entry.mentioned.0
                        && entry.zone == zone
                })
        },
    )]
    fn push(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
        declared: Maybe<NodeIndex, binder_type::Absent>,
        site: Maybe<ByteSpan, binder_site::Absent>,
        zone: Zone,
    ) -> ScopeId
    {
        let minted = ScopeId(self.frames.len());
        self.frames.push(ScopeFrame {
            name,
            parent,
            declared,
            mentioned: Mentioned(false),
            quoted: Mentioned(false),
            site,
            zone,
        });

        minted
    }

    /// Where the binder that introduced `binder` was written.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range coordinate is admissible.
    /// - ensures: a stored frame answers the site it was extended with; an
    ///   out-of-range coordinate answers the unwritten absence.
    /// - provides: the use-to-binder half a minted variable records.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written binder, an unwritten frame and an
    ///   out-of-range coordinate answer their exact sites.
    /// - witness: `resolve::tests::a_frame_keeps_its_binder_s_span`
    #[spec(ensures: |ret| ret == self.frames.get(binder.0)
        .map_or(Maybe::Absent(binder_site::Absent::Unwritten), |entry| entry.site))]
    #[inline]
    pub fn site(
        &self,
        binder: ScopeId,
    ) -> Maybe<ByteSpan, binder_site::Absent>
    {
        self.frames
            .get(binder.0)
            .map_or(Maybe::Absent(binder_site::Absent::Unwritten), |entry| {
                entry.site
            })
    }

    /// The zone the binder that introduced `binder` binds into.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range coordinate is admissible.
    /// - ensures: a stored frame answers the zone it was extended into; an
    ///   out-of-range coordinate answers the intuitionistic zone, the zone of
    ///   every binder but a fork's ends.
    /// - provides: the zone a minted variable is read in.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a linear and an intuitionistic frame of one chain
    ///   answer their own zones.
    /// - witness: `resolve::tests::a_linear_binder_counts_apart_from_intuitionistic_ones`
    #[spec(ensures: |ret| ret == self.frames.get(binder.0).map_or(Zone::Intuitionistic, |entry| entry.zone))]
    #[inline]
    #[must_use]
    pub fn zone(
        &self,
        binder: ScopeId,
    ) -> Zone
    {
        self.frames
            .get(binder.0)
            .map_or(Zone::Intuitionistic, |entry| entry.zone)
    }

    /// The type the binder that introduced `binder` was written with.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range coordinate is admissible.
    /// - ensures: a stored frame answers the syntax node of its written type,
    ///   or the untyped absence it was extended with; an out-of-range
    ///   coordinate answers the untyped absence.
    /// - provides: the type a derived path operation reads off a parameter it
    ///   stands over.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a typed and an untyped frame of one chain answer
    ///   their own written types.
    /// - witness: `resolve::tests::a_typed_binder_resolves_with_its_written_type`
    #[spec(ensures: |ret| ret == self.frames.get(binder.0)
        .map_or(Maybe::Absent(binder_type::Absent::Untyped), |entry| entry.declared))]
    #[inline]
    pub fn declared(
        &self,
        binder: ScopeId,
    ) -> Maybe<NodeIndex, binder_type::Absent>
    {
        self.frames
            .get(binder.0)
            .map_or(Maybe::Absent(binder_type::Absent::Untyped), |entry| {
                entry.declared
            })
    }

    /// The linear index the binder `binder` has in the chain rooted at `from`.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range coordinate is admissible.
    /// - ensures: when `binder` is on the chain, the number of linear frames
    ///   strictly between `from` and it; the unbound absence otherwise.
    /// - provides: where a slot a loop holds again stands at a pass's end,
    ///   whatever name binds closer.
    /// - fails: never.
    /// - panics: none. Parent links name an earlier frame, so the walk ends.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an outer slot found past a shadow of its name and a
    ///   view, an intuitionistic frame between counting nothing, and a binder
    ///   off the chain answered absent.
    /// - witness: `resolve::tests::a_linear_binder_is_found_by_its_coordinate`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(index) => usize::try_from(u32::from(index)).is_ok_and(|depth| depth < self.frames.len()),
        | Maybe::Absent(binder::Absent::Unbound) => true,
    })]
    #[inline]
    pub fn linear_index(
        &self,
        from: Frame,
        binder: ScopeId,
    ) -> Maybe<DeBruijnIndex, binder::Absent>
    {
        let mut linear = 0_u32;
        for here in self.chain(from) {
            if here == binder {
                return Maybe::Present(DeBruijnIndex::from(linear));
            }
            if self.zone(here) == Zone::Linear {
                linear = linear.saturating_add(1_u32);
            }
        }
        Maybe::Absent(binder::Absent::Unbound)
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
    /// - ensures: on a hit, the number of binders of the hit's zone strictly
    ///   between the use site and the innermost binder of `name` — zero at the
    ///   innermost such binder, so an inner binder shadows an outer one of the
    ///   same name whatever their zones — with the type that binder was written
    ///   with and its zone; the unbound absence when no binder in the chain
    ///   carries the name.
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
                let mut walked = 0_usize;
                let mut linear = 0_usize;
                let mut intuitionistic = 0_usize;
                let expected = loop {
                    let Frame::Inner(id) = current
                    else {
                        break Maybe::Absent(binder::Absent::Unbound);
                    };
                    if walked >= self.frames.len() {
                        return false;
                    }
                    let Some(entry) = self.frames.get(id.0)
                    else {
                        return false;
                    };
                    let depth = if entry.zone == Zone::Linear { linear } else { intuitionistic };
                    if entry.name == name {
                        break Maybe::Present(Bound {
                            index: DeBruijnIndex::from(u32::try_from(depth).unwrap_or(u32::MAX)),
                            binder: id,
                            declared: entry.declared,
                            zone: entry.zone,
                        });
                    }
                    walked = walked.saturating_add(1);
                    if entry.zone == Zone::Linear {
                        linear = linear.saturating_add(1);
                    }
                    else {
                        intuitionistic = intuitionistic.saturating_add(1);
                    }
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
        let mut linear = 0_usize;
        let mut intuitionistic = 0_usize;
        while let Frame::Inner(ScopeId(position)) = current {
            fuel.spend()?;
            let Some(entry) = self.frames.get(position)
            else {
                break;
            };
            let depth = match entry.zone {
                Zone::Linear => &mut linear,
                Zone::Intuitionistic => &mut intuitionistic,
            };
            if entry.name.as_ref() == spelled {
                let index = u32::try_from(*depth).unwrap_or(u32::MAX);

                return Ok(Maybe::Present(Bound {
                    index: DeBruijnIndex::from(index),
                    binder: ScopeId(position),
                    declared: entry.declared,
                    zone: entry.zone,
                }));
            }
            *depth = depth.saturating_add(1_usize);
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

    /// Record that a type quoted in a body names the binder that introduced
    /// `binder`.
    ///
    /// # Specification
    /// - requires: nothing — the coordinate is interpreted in this scope.
    /// - ensures: a stored frame binds in [`Telescope::Quote`] from now on; its
    ///   mention, which makes the signature's arrow dependent, is unchanged.
    /// - provides: the body quote's half of the telescope decision, apart from
    ///   the signature's (#547).
    /// - fails: never; an out-of-range coordinate is ignored.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quoted binder binds in a body quote's telescope and
    ///   not in the signature's.
    /// - witness: `resolve::tests::a_quoted_binder_binds_only_in_a_body_quote_s_telescope`
    #[spec(
        captures: before = (self.frames.len(), self.mentioned(binder)),
        ensures: self.frames.len() == before.0
            && self.mentioned(binder) == before.1
            && self
                .frames
                .get(binder.0)
                .is_none_or(|entry| entry.quoted.0),
    )]
    #[inline]
    pub fn quote(
        &mut self,
        binder: ScopeId,
    )
    {
        if let Some(entry) = self.frames.get_mut(binder.0) {
            entry.quoted = Mentioned(true);
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

    /// Whether the binder that introduced `binder` binds in `telescope`: a
    /// type of that telescope names it, or it is written with no type.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range coordinate is admissible.
    /// - ensures: a stored frame answers whether it binds in `telescope`; an
    ///   out-of-range coordinate answers false.
    /// - provides: whether a type introducing `binder` depends on it, read in
    ///   the telescope the type's reads counted it in (#583).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mentioned binder, a quoted one and one neither
    ///   names, each asked in both telescopes.
    /// - witness: `resolve::tests::a_quoted_binder_binds_only_in_a_body_quote_s_telescope`
    #[spec(
        ensures: |ret| {
            ret.0
                == self
                    .frames
                    .get(binder.0)
                    .is_some_and(|entry| entry.binds_in(telescope).0)
        },
    )]
    #[inline]
    #[must_use]
    pub fn binds(
        &self,
        binder: ScopeId,
        telescope: Telescope,
    ) -> Mentioned
    {
        self.frames
            .get(binder.0)
            .map_or(Mentioned(false), |entry| entry.binds_in(telescope))
    }

    /// The de Bruijn index the binder `binder` has from `from` in the
    /// signature's telescope: [`Self::index_in`] at [`Telescope::Signature`].
    ///
    /// # Specification
    /// - requires: as [`Self::index_in`].
    /// - ensures: as [`Self::index_in`], counting a typed binder only when a
    ///   signature's type position names it.
    /// - provides: the index a decode in a function tail's signature carries.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mentioned typed binder, an unmentioned one and an
    ///   untyped one between the use site and the binder, each asserted to
    ///   count or not.
    /// - witness: `resolve::tests::only_a_mentioned_typed_binder_counts_in_a_telescope`
    #[spec(ensures: |ret| ret == self.index_in(from, binder, Telescope::Signature))]
    #[inline]
    #[must_use]
    pub fn telescope_index(
        &self,
        from: Frame,
        binder: ScopeId,
    ) -> DeBruijnIndex
    {
        self.index_in(from, binder, Telescope::Signature)
    }

    /// The de Bruijn index the binder `binder` has from `from` in
    /// `telescope`: the binders strictly between, counting a typed binder only
    /// when a type of that telescope names it.
    ///
    /// # Specification
    /// - requires: `from` is outermost or an existing frame position in the
    ///   intended scope; every mention has been recorded.
    /// - ensures: counts from `from` up to but excluding `binder`, including
    ///   each untyped intuitionistic frame and each typed one that binds in
    ///   `telescope`. If the target is not on the chain, counts to its end; a
    ///   typed frame that does not bind and a linear frame contribute nothing.
    ///   The count saturates at the index width.
    /// - provides: the index a decode in a signature, or in a type a body
    ///   quotes, carries.
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
    /// - witness: `resolve::tests::a_quoted_binder_binds_only_in_a_body_quote_s_telescope`
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
                if entry.binds_in(telescope).0 {
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
    pub fn index_in(
        &self,
        from: Frame,
        binder: ScopeId,
        telescope: Telescope,
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
            if entry.binds_in(telescope).0 {
                depth = depth.saturating_add(1_u32);
            }
            current = entry.parent;
        }

        DeBruijnIndex::from(depth)
    }

    /// Whether each frame of the chain rooted at `from` binds in a telescope,
    /// innermost first: an untyped frame always, a typed one when a type
    /// position names it.
    ///
    /// # Specification
    /// - requires: `from` is outermost or an existing frame position; every
    ///   mention has been recorded.
    /// - ensures: one answer per intuitionistic frame from `from` to the
    ///   outermost, in that order, each the rule [`Self::telescope_index`]
    ///   counts by; nothing for a linear frame, which no type names, and
    ///   nothing for the outermost frame.
    /// - provides: the difference between a type's telescope indices and the
    ///   term indices of the same chain, which relocating a type into a term
    ///   reads.
    /// - fails: never.
    /// - panics: none. The walk follows parent links, which always name an
    ///   earlier frame, so it ends.
    /// - executable: none — the specification facade wraps the body in a
    ///   closure, which cannot return the opaque iterator; the witness checks
    ///   each answer of a chain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mentioned typed frame, an unmentioned one and an
    ///   untyped one, each reported in chain order, and a linear frame between
    ///   them reported not at all.
    /// - witness: `resolve::tests::a_chain_reports_which_frames_bind_in_a_telescope`
    /// - witness: `resolve::tests::a_linear_binder_counts_apart_from_intuitionistic_ones`
    #[inline]
    pub fn telescope_binders(
        &self,
        from: Frame,
    ) -> impl Iterator<Item = bool> + '_
    {
        self.binders_in(from, Telescope::Signature)
    }

    /// Whether each frame of the chain rooted at `from` binds in `telescope`,
    /// innermost first, by the rule [`Self::index_in`] counts by; nothing for
    /// a linear frame.
    ///
    /// # Specification
    /// - requires: as [`Self::telescope_binders`].
    /// - ensures: as [`Self::telescope_binders`], in `telescope`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::telescope_binders`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quoted binder binds in a body quote's telescope and
    ///   not in the signature's.
    /// - witness: `resolve::tests::a_quoted_binder_binds_only_in_a_body_quote_s_telescope`
    #[inline]
    pub fn binders_in(
        &self,
        from: Frame,
        telescope: Telescope,
    ) -> impl Iterator<Item = bool> + '_
    {
        let first = match from {
            Frame::Inner(id) => Some(id),
            Frame::Outermost => None,
        };
        core::iter::successors(first, |id| match self.frames.get(id.0)?.parent {
            Frame::Inner(parent) => Some(parent),
            Frame::Outermost => None,
        })
        .filter_map(move |id| match self.frames.get(id.0) {
            Some(entry) if entry.zone == Zone::Linear => None,
            Some(entry) => Some(entry.binds_in(telescope).0),
            None => Some(true),
        })
    }

    /// The frames of the chain rooted at `from`, from `from` to the outermost.
    ///
    /// # Specification
    /// - requires: `from` is outermost or an existing frame position.
    /// - ensures: `from`'s own frame first, then each parent in turn; nothing
    ///   for the outermost frame.
    /// - fails: never.
    /// - panics: none. Parent links name an earlier frame, so the walk ends.
    /// - executable: none — the specification facade wraps the body in a
    ///   closure, which cannot return the opaque iterator; the witness counts a
    ///   chain's scopes through it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a capability at the inner of two nested scopes counts
    ///   both; a walk stopping early or skipping a frame miscounts the depth.
    /// - witness: `lower::capability::tests::a_capability_at_a_scope_lives_in_its_region`
    #[inline]
    pub fn chain(
        &self,
        from: Frame,
    ) -> impl Iterator<Item = ScopeId> + '_
    {
        let first = match from {
            Frame::Inner(id) => Some(id),
            Frame::Outermost => None,
        };
        core::iter::successors(first, |id| match self.frames.get(id.0)?.parent {
            Frame::Inner(parent) => Some(parent),
            Frame::Outermost => None,
        })
    }

    /// The names of the frames of the chain rooted at `from` that bind in
    /// `telescope`, outermost first: the context a type read under `from` in
    /// that telescope is spelled in.
    ///
    /// # Specification
    /// - requires: as [`Self::telescope_binders`].
    /// - ensures: one name per frame [`Self::binders_in`] answers true for at
    ///   `telescope`, in the reverse of its order, so the last names index
    ///   zero.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mentioned typed frame and an untyped one are named
    ///   in the signature's telescope, an unmentioned typed one is not; a
    ///   quoted one is named in a body quote's alone (#590).
    /// - witness: `resolve::tests::a_chain_reports_which_frames_bind_in_a_telescope`
    /// - witness: `resolve::tests::a_quoted_binder_binds_only_in_a_body_quote_s_telescope`
    #[spec(ensures: |ret| ret.len() == self.binders_in(from, telescope).filter(|&binds| binds).count())]
    #[inline]
    #[must_use]
    pub fn telescope_names(
        &self,
        from: Frame,
        telescope: Telescope,
    ) -> Vec<SurfaceName<'source>>
    {
        let first = match from {
            Frame::Inner(id) => Some(id),
            Frame::Outermost => None,
        };
        let mut names: Vec<SurfaceName<'source>> =
            core::iter::successors(first, |id| match self.frames.get(id.0)?.parent {
                Frame::Inner(parent) => Some(parent),
                Frame::Outermost => None,
            })
            .filter_map(|id| {
                let entry = self.frames.get(id.0)?;
                entry.binds_in(telescope).0.then_some(entry.name)
            })
            .collect();
        names.reverse();
        names
    }

    /// The binders in scope at each span of `read`: this scope's frames, each
    /// with its binder's written name and the frame it extends, beside `read`,
    /// each span the lowering read under a binder with the innermost frame it
    /// was read under.
    ///
    /// # Specification
    /// - requires: every frame of `read` is a position of this scope.
    /// - ensures: one frame per frame of this scope, in order, keeping its site
    ///   and parent; `read` ascending by start then end, duplicates dropped;
    ///   the widest read span's width.
    /// - provides: the table [`InScope::binders_at`] answers from, built once
    ///   per lowering.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the frames and one sort of `read`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`InScope::binders_at`].
    /// - witness: `tests::scopes::the_binders_in_scope_are_the_innermost_reading_s_chain`
    #[spec(ensures: |ret| ret.frames.len() == self.frames.len()
        && ret.read.windows(2).all(|pair| matches!(*pair, [(first, _), (second, _)] if (first.start(), first.end()) < (second.start(), second.end()) || (first.start(), first.end()) == (second.start(), second.end()))))]
    #[inline]
    #[must_use]
    pub fn in_scope(
        &self,
        mut read: Vec<(ByteSpan, ScopeId)>,
    ) -> InScope
    {
        read.sort_by_key(|&(span, frame)| (span.start(), span.end(), frame));
        read.dedup();
        let widest = read
            .iter()
            .map(|&(span, _)| usize::from(span.end()).saturating_sub(usize::from(span.start())))
            .max()
            .unwrap_or(0_usize);
        InScope {
            frames: self
                .frames
                .iter()
                .map(|frame| (frame.site, frame.parent))
                .collect(),
            read,
            widest,
        }
    }

    /// [`Self::in_scope`] over `prior`'s read spans followed by `read`, when
    /// `prior` is the table a lowering of a prefix of this scope's text built
    /// and every span of `read` follows each of `prior`'s.
    ///
    /// # Specification
    /// - requires: every frame of `read` is a position of this scope; every
    ///   span of `read` starts at or after the end of each of `prior`'s.
    /// - ensures: one frame per frame of this scope, in order, keeping its site
    ///   and parent; `prior`'s read spans then `read`'s, ascending by start
    ///   then end, duplicates dropped; the widest of both.
    /// - provides: the table of a lowering resumed after a closure's, built in
    ///   the size of the spans read after it.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the frames, one sort of `read`, one copy of
    ///   `prior`'s spans.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document resumed after its closure keeps the table
    ///   the whole lowering builds.
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(
        requires: prior.read.last().is_none_or(|&(last, _)| read.iter().all(|&(span, _)| span.start() >= last.end())),
        captures: added = read.len(),
        ensures: |ret| ret.frames.len() == self.frames.len()
            && ret.read.len() <= prior.read.len().saturating_add(added),
    )]
    #[must_use]
    pub(crate) fn in_scope_after(
        &self,
        prior: &InScope,
        read: Vec<(ByteSpan, ScopeId)>,
    ) -> InScope
    {
        let InScope {
            frames,
            read: own,
            widest,
        } = self.in_scope(read);
        let mut all = Vec::with_capacity(prior.read.len().saturating_add(own.len()));
        all.extend_from_slice(&prior.read);
        all.extend(own);
        InScope {
            frames,
            read: all,
            widest: prior.widest.max(widest),
        }
    }
}

/// The binders in scope at each offset of a lowered text.
///
/// Every frame the lowering minted is kept with its binder's written name and
/// the frame it extends, and every span it read under a binder with the
/// innermost frame it was read under. A declaration the lowering refused keeps
/// its spans and frames, so a name not yet written in full is read in scope.
///
/// # Specification
/// - requires: built by [`Scope::in_scope`].
/// - ensures: every frame of `read` is a position of `frames`, every parent an
///   earlier one; `read` ascends by start then end; `widest` is at least every
///   read span's width.
/// - provides: the binders a name written at an offset would resolve to.
/// - executable: none — a carrier; [`Scope::in_scope`] and
///   [`InScope::binders_at`] carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`InScope::binders_at`].
/// - witness: `tests::scopes::the_binders_in_scope_are_the_innermost_reading_s_chain`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InScope
{
    /// Each frame, by position: its binder's written name, when written, and
    /// the frame it extends.
    frames: Vec<(Maybe<ByteSpan, binder_site::Absent>, Frame)>,
    /// Each span read under a binder, with the innermost frame it was read
    /// under, ascending by start then end.
    read: Vec<(ByteSpan, ScopeId)>,
    /// The widest read span's width in bytes.
    widest: usize,
}

impl InScope
{
    /// The written names of the binders in scope at `offset`, innermost
    /// first, a shadowed binder included.
    ///
    /// # Specification
    /// - requires: nothing; any offset is admitted.
    /// - ensures: the narrowest read span starting at or before `offset` and
    ///   ending after it, the earliest among equals; then the name of each
    ///   frame of its frame's chain that has one, from that frame outward;
    ///   nothing when no read span holds `offset`.
    /// - provides: the binders a completion at `offset` offers.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator over the chain, drawn
    ///   as the caller draws it.
    /// - intension: a binary search for the spans starting at or before
    ///   `offset`, a walk back over those no wider than the widest, then one
    ///   step per frame of the chain.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter in its body and out of it, a pattern's
    ///   binder in its arm and in a sibling arm, a lambda's binder, and the
    ///   binders of a declaration the lowering refused, each asserted at their
    ///   exact names.
    /// - witness: `tests::scopes::the_binders_in_scope_are_the_innermost_reading_s_chain`
    /// - witness: `tests::scopes::the_binders_in_scope_are_kept_for_a_refused_declaration_831`
    #[inline]
    pub fn binders_at(
        &self,
        offset: ByteOffset,
    ) -> impl Iterator<Item = ByteSpan> + '_
    {
        let after = self
            .read
            .partition_point(|&(span, _)| span.start() <= offset);
        let mut innermost: Option<(ByteSpan, ScopeId)> = None;
        for &(span, frame) in self.read.get(.. after).unwrap_or_default().iter().rev() {
            if usize::from(offset).saturating_sub(usize::from(span.start())) > self.widest {
                break;
            }
            let width =
                |held: ByteSpan| usize::from(held.end()).saturating_sub(usize::from(held.start()));
            if offset < span.end() && innermost.is_none_or(|(held, _)| width(span) <= width(held)) {
                innermost = Some((span, frame));
            }
        }
        core::iter::successors(innermost.map(|(_, frame)| frame), |frame| {
            match self.frames.get(frame.0)?.1 {
                Frame::Inner(parent) => Some(parent),
                Frame::Outermost => None,
            }
        })
        .filter_map(|frame| match self.frames.get(frame.0)?.0 {
            Maybe::Present(site) => Some(site),
            Maybe::Absent(_) => None,
        })
    }
}

/// What a written name the lowering resolved names.
///
/// The lowering records a name's resolution when it resolves it, before the
/// declaration holding the name is lowered whole, so a declaration it refuses
/// keeps every name it resolved before the refusal.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Resolution
{
    /// The binder written at this span.
    Binder(ByteSpan),
    /// The declaration admitted at this position.
    Declaration(ConstantIndex),
    /// A constructor.
    Constructor
    {
        /// The constructor's name tile, where its family's form writes it.
        named: ByteSpan,
        /// The family's admission position.
        family: ConstantIndex,
    },
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::NodeIndex;
    use quenchant_shape::shape::Maybe;

    use super::Bound;
    use super::Frame;
    use super::Scope;
    use super::ScopeId;
    use super::SurfaceName;
    use super::Telescope;
    use super::TypeFormer;
    use super::binder;
    use super::binder_site;
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

    /// A frame no written binder enters.
    const UNWRITTEN: Maybe<ByteSpan, binder_site::Absent> =
        Maybe::Absent(binder_site::Absent::Unwritten);

    #[test]
    fn a_frame_keeps_its_binder_s_span()
    {
        let written = ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(5_usize)).unwrap();
        let mut scope = Scope::new();
        let named = scope.extend(
            Frame::Outermost,
            SurfaceName::from("x"),
            Maybe::Present(written),
        );
        let hidden = scope.extend(Frame::Inner(named), SurfaceName::from(""), UNWRITTEN);
        assert_eq!(
            scope.site(named),
            Maybe::Present(written),
            "a written binder keeps its span"
        );
        assert_eq!(
            scope.site(hidden),
            UNWRITTEN,
            "an unwritten frame keeps none"
        );
        let mut other = Scope::new();
        let _only = other.extend(Frame::Outermost, SurfaceName::from("y"), UNWRITTEN);
        assert_eq!(
            other.site(hidden),
            UNWRITTEN,
            "a coordinate past the scope's frames answers none"
        );
    }

    #[test]
    fn binder_positions_do_not_authenticate_their_minting_scope()
    {
        let mut first = Scope::new();
        let foreign = first.extend(Frame::Outermost, SurfaceName::from("foreign"), UNWRITTEN);
        let outside = first.extend(
            Frame::Inner(foreign),
            SurfaceName::from("outside"),
            UNWRITTEN,
        );
        let mut receiving = Scope::new();
        let local = receiving.extend(Frame::Outermost, SurfaceName::from("local"), UNWRITTEN);
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
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("y"), UNWRITTEN);
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
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("outer"), UNWRITTEN);
        let typed = scope.extend_typed(
            Frame::Inner(outer),
            SurfaceName::from("typed"),
            NodeIndex::from(7_usize),
            UNWRITTEN,
        );
        let inner = scope.extend(Frame::Inner(typed), SurfaceName::from("inner"), UNWRITTEN);
        let sibling = scope.extend(Frame::Outermost, SurfaceName::from("sibling"), UNWRITTEN);
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
        let expected = [
            ("+U", TypeFormer::Thunk),
            ("-F", TypeFormer::Returner),
            ("List", TypeFormer::List),
            ("Run", TypeFormer::Run),
        ];

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
        let inner = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);

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
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("y"), UNWRITTEN);

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
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("x"), UNWRITTEN);

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
        let shared = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);
        let left = scope.extend(Frame::Inner(shared), SurfaceName::from("y"), UNWRITTEN);
        let right = scope.extend(Frame::Inner(shared), SurfaceName::from("z"), UNWRITTEN);

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
        let frame = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);

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
        let outer = scope.extend(Frame::Outermost, SurfaceName::from("x"), UNWRITTEN);
        let inner = scope.extend(Frame::Inner(outer), SurfaceName::from("y"), UNWRITTEN);
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
            UNWRITTEN,
        );
        let untyped = scope.extend(Frame::Inner(typed), SurfaceName::from("x"), UNWRITTEN);

        assert_eq!(
            scope.resolve(Frame::Inner(untyped), SurfaceName::from("a"), &mut tank()),
            Ok(Maybe::Present(Bound {
                index: DeBruijnIndex::from(1_u32),
                binder: typed,
                declared: Maybe::Present(NodeIndex::from(7_usize)),
                zone: Zone::Intuitionistic,
            })),
            "a typed binder answers the node its type was written at"
        );
        assert_eq!(
            scope.resolve(Frame::Inner(untyped), SurfaceName::from("x"), &mut tank()),
            Ok(Maybe::Present(Bound {
                index: DeBruijnIndex::from(0_u32),
                binder: untyped,
                declared: Maybe::Absent(binder_type::Absent::Untyped),
                zone: Zone::Intuitionistic,
            })),
            "an untyped binder answers no written type"
        );
        assert_eq!(
            (
                scope.declared(typed),
                scope.declared(untyped),
                scope.declared(ScopeId(9)),
            ),
            (
                Maybe::Present(NodeIndex::from(7_usize)),
                Maybe::Absent(binder_type::Absent::Untyped),
                Maybe::Absent(binder_type::Absent::Untyped),
            ),
            "each frame answers its own written type, and a stray coordinate none"
        );
    }

    #[test]
    fn only_a_mentioned_typed_binder_counts_in_a_telescope()
    {
        let mut scope = Scope::new();
        let typed = |scope: &mut Scope<'static>, parent: Frame, name: &'static str| {
            scope.extend_typed(
                parent,
                SurfaceName::from(name),
                NodeIndex::from(1_usize),
                UNWRITTEN,
            )
        };
        let a = typed(&mut scope, Frame::Outermost, "a");
        let b = typed(&mut scope, Frame::Inner(a), "b");
        let x = typed(&mut scope, Frame::Inner(b), "x");
        let y = scope.extend(Frame::Inner(x), SurfaceName::from("y"), UNWRITTEN);
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

    #[test]
    fn a_quoted_binder_binds_only_in_a_body_quote_s_telescope()
    {
        use alloc::vec::Vec;

        let mut scope = Scope::new();
        let typed = |scope: &mut Scope<'static>, parent: Frame, name: &'static str| {
            scope.extend_typed(
                parent,
                SurfaceName::from(name),
                NodeIndex::from(1_usize),
                UNWRITTEN,
            )
        };
        let x = typed(&mut scope, Frame::Outermost, "x");
        let a = typed(&mut scope, Frame::Inner(x), "a");
        let n = typed(&mut scope, Frame::Inner(a), "n");
        scope.mention(x);
        scope.quote(a);

        assert!(
            !bool::from(scope.mentioned(a)),
            "a body quote's read leaves the signature's arrow independent"
        );
        assert_eq!(
            scope.telescope_index(Frame::Inner(n), x),
            DeBruijnIndex::from(0_u32),
            "the signature's telescope skips the quoted binder"
        );
        assert_eq!(
            scope.index_in(Frame::Inner(n), x, Telescope::Quote),
            DeBruijnIndex::from(1_u32),
            "a body quote's telescope counts it"
        );
        assert_eq!(
            scope
                .binders_in(Frame::Inner(n), Telescope::Quote)
                .collect::<Vec<_>>(),
            Vec::from([false, true, true]),
            "innermost first: the unnamed binder, the quoted one, the mentioned one"
        );
        assert_eq!(
            scope.telescope_binders(Frame::Inner(n)).collect::<Vec<_>>(),
            Vec::from([false, false, true])
        );
        assert_eq!(
            [x, a, n].map(|binder| {
                [Telescope::Signature, Telescope::Quote]
                    .map(|telescope| bool::from(scope.binds(binder, telescope)))
            }),
            [[true, true], [false, true], [false, false]],
            "the mentioned binder binds in both, the quoted one in a body quote's alone, the \
             unnamed one in neither"
        );
        assert_eq!(
            [Telescope::Signature, Telescope::Quote]
                .map(|telescope| scope.telescope_names(Frame::Inner(n), telescope)),
            [
                Vec::from([SurfaceName::from("x")]),
                Vec::from([SurfaceName::from("x"), SurfaceName::from("a")])
            ],
            "a type a body quotes is spelled with the quoted binder's name (#590)"
        );
    }

    #[test]
    fn a_chain_reports_which_frames_bind_in_a_telescope()
    {
        use alloc::vec::Vec;

        let mut scope = Scope::new();
        let a = scope.extend_typed(
            Frame::Outermost,
            SurfaceName::from("a"),
            NodeIndex::from(1_usize),
            UNWRITTEN,
        );
        let x = scope.extend_typed(
            Frame::Inner(a),
            SurfaceName::from("x"),
            NodeIndex::from(2_usize),
            UNWRITTEN,
        );
        let y = scope.extend(Frame::Inner(x), SurfaceName::from("y"), UNWRITTEN);
        scope.mention(a);

        assert_eq!(
            scope.telescope_binders(Frame::Inner(y)).collect::<Vec<_>>(),
            Vec::from([true, false, true]),
            "innermost first: the untyped frame, the unmentioned typed one, the mentioned one"
        );
        assert_eq!(
            scope.telescope_names(Frame::Inner(y), Telescope::Signature),
            Vec::from([SurfaceName::from("a"), SurfaceName::from("y")]),
            "outermost first, the unmentioned typed frame unnamed"
        );
        assert_eq!(
            scope.telescope_binders(Frame::Outermost).count(),
            0,
            "the outermost frame binds nothing"
        );
    }

    #[test]
    fn a_linear_binder_counts_apart_from_intuitionistic_ones()
    {
        use alloc::vec::Vec;

        let mut scope = Scope::new();
        let a = scope.extend(Frame::Outermost, SurfaceName::from("a"), UNWRITTEN);
        let c = scope.extend_linear(Frame::Inner(a), SurfaceName::from("c"), UNWRITTEN);
        let x = scope.extend(Frame::Inner(c), SurfaceName::from("x"), UNWRITTEN);
        let shadow = scope.extend_linear(Frame::Inner(x), SurfaceName::from("x"), UNWRITTEN);
        let y = scope.extend(Frame::Inner(shadow), SurfaceName::from("y"), UNWRITTEN);
        let at = |scope: &Scope<'static>, name: &'static str| {
            scope.resolve(Frame::Inner(y), SurfaceName::from(name), &mut tank())
        };
        let bound = |index: u32, binder, zone| {
            Ok(Maybe::Present(Bound {
                index: DeBruijnIndex::from(index),
                binder,
                declared: Maybe::Absent(binder_type::Absent::Untyped),
                zone,
            }))
        };

        assert_eq!(
            at(&scope, "a"),
            bound(2, a, Zone::Intuitionistic),
            "an intuitionistic index passes the linear frames by"
        );
        assert_eq!(
            at(&scope, "c"),
            bound(1, c, Zone::Linear),
            "a linear index passes the intuitionistic frames by"
        );
        assert_eq!(
            at(&scope, "x"),
            bound(0, shadow, Zone::Linear),
            "the innermost binder shadows whatever its zone"
        );
        assert_eq!(
            (scope.zone(c), scope.zone(x)),
            (Zone::Linear, Zone::Intuitionistic)
        );
        assert_eq!(
            scope.telescope_binders(Frame::Inner(y)).collect::<Vec<_>>(),
            Vec::from([true, true, true]),
            "a telescope reports the intuitionistic frames alone"
        );
        assert_eq!(
            scope.telescope_index(Frame::Inner(y), a),
            DeBruijnIndex::from(2_u32)
        );
    }

    #[test]
    fn a_linear_binder_is_found_by_its_coordinate()
    {
        let mut scope = Scope::new();
        let held = scope.extend_linear(Frame::Outermost, SurfaceName::from("n"), UNWRITTEN);
        let pass = scope.extend(Frame::Inner(held), SurfaceName::from("s"), UNWRITTEN);
        let shadow = scope.extend_linear(Frame::Inner(pass), SurfaceName::from("n"), UNWRITTEN);
        let view = scope.extend_linear(Frame::Inner(shadow), SurfaceName::from("v"), UNWRITTEN);
        let elsewhere = scope.extend_linear(Frame::Outermost, SurfaceName::from("m"), UNWRITTEN);

        assert_eq!(
            scope.linear_index(Frame::Inner(view), held),
            Maybe::Present(DeBruijnIndex::from(2_u32)),
            "the outer slot is reached past the shadow and the view, whatever the name"
        );
        assert_eq!(
            scope.linear_index(Frame::Inner(view), shadow),
            Maybe::Present(DeBruijnIndex::from(1_u32)),
            "the intuitionistic frame between counts nothing"
        );
        assert_eq!(
            scope.linear_index(Frame::Inner(view), elsewhere),
            Maybe::Absent(binder::Absent::Unbound),
            "a binder off the chain is not found"
        );
    }
}
