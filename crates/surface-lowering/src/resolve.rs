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

use gandr_kernel_term::DeBruijnIndex;
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
const TYPE_ATOMS: [(&str, TypeAtom); 3_usize] = [
    ("Unit", TypeAtom::Unit),
    ("Integer", TypeAtom::Integer),
    ("String", TypeAtom::Text),
];

/// The unary type heads, with the spellings the surface writes them as.
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(usize);

/// The binder frame a term is read under.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Frame
{
    /// Under no binder: a declaration's own body, or an attribute payload.
    Outermost,
    /// Under the binder this frame names, and every binder it extends.
    Inner(ScopeId),
}

/// One binder, and the frame it extends.
#[derive(Clone, Copy, Debug)]
struct ScopeFrame<'source>
{
    /// The name this binder introduces.
    name: SurfaceName<'source>,
    /// The frame this one extends.
    parent: Frame,
}

/// Every binder frame one lowering minted, as a persistent chain.
///
/// The chain is flat and id-addressed rather than pointer-linked: a frame names
/// its parent by position in this vector, so a scope is shared by every node
/// under one binder without being copied and without a drop that walks depth.
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

    /// The frame that extends `parent` with a binder for `name`.
    ///
    /// # Specification
    /// - requires: `parent` was minted by this scope, or is the outermost
    ///   frame.
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
    #[inline]
    pub fn extend(
        &mut self,
        parent: Frame,
        name: SurfaceName<'source>,
    ) -> ScopeId
    {
        let minted = ScopeId(self.frames.len());
        self.frames.push(ScopeFrame { name, parent });

        minted
    }

    /// The de Bruijn index `name` has in the chain rooted at `frame`.
    ///
    /// # Specification
    /// - requires: `frame` was minted by this scope, or is the outermost frame;
    ///   `fuel` holds the lowering's remaining allowance.
    /// - ensures: on a hit, the number of binders strictly between the use site
    ///   and the innermost binder of `name` — zero at the innermost binder, so
    ///   an inner binder shadows an outer one of the same name; the unbound
    ///   absence when no binder in the chain carries the name.
    /// - provides: the binder half of term-name resolution, and the only place
    ///   a surface name becomes a de Bruijn index.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the chain walk outruns
    ///   the lowering's allowance, which is what bounds an otherwise quadratic
    ///   walk over a deep binder chain.
    /// - panics: none. The index narrows with a saturating conversion whose
    ///   ceiling is unreachable: one step of allowance is spent per frame, so a
    ///   chain longer than the index width costs more allowance than a budget
    ///   can hold.
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
    #[inline]
    pub fn index_of<'refusal>(
        &self,
        frame: Frame,
        name: SurfaceName<'_>,
        fuel: &mut Fuel,
    ) -> Result<Maybe<DeBruijnIndex, binder::Absent>, LoweringRefusal<'refusal>>
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

                return Ok(Maybe::Present(DeBruijnIndex::from(index)));
            }
            depth = depth.saturating_add(1_usize);
            current = entry.parent;
        }

        Ok(Maybe::Absent(binder::Absent::Unbound))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;

    use gandr_kernel_term::DeBruijnIndex;
    use quenchant_shape::shape::Maybe;

    use super::Frame;
    use super::HeadArity;
    use super::OperandCount;
    use super::Scope;
    use super::SurfaceName;
    use super::TypeAtom;
    use super::TypeFormer;
    use super::binder;
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
        assert_eq!(
            expected.len(),
            3_usize,
            "the fragment admits exactly three nullary type heads"
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
        let expected = [("+U", TypeFormer::Thunk), ("-F", TypeFormer::Returner)];

        for (spelling, former) in expected {
            assert_eq!(
                type_former(SurfaceName::from(spelling)),
                Maybe::Present(former),
                "the unary table is pinned row by row"
            );
        }
        assert_eq!(
            expected.len(),
            2_usize,
            "the fragment admits exactly two unary type heads"
        );
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
    fn a_head_arity_renders_how_the_head_was_written()
    {
        assert_eq!(
            format!("{}", HeadArity::Nullary),
            String::from("bare"),
            "the nullary arity renders as the bare spelling"
        );
        assert_eq!(
            format!("{}", HeadArity::Unary),
            String::from("applied to one argument"),
            "the unary arity renders as the applied spelling"
        );
        assert_eq!(
            format!("{}", HeadArity::Polyadic(OperandCount::from(3_usize))),
            String::from("applied to 3 arguments"),
            "a polyadic arity renders its argument count"
        );
    }
}
