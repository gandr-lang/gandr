//! Declarations as data: the prenex level signature, the three live content
//! shapes, the admission mark that rides with each declaration in an artifact,
//! and the borrowing builder that ties content minting to the arena watermark.
//!
//! Nothing here admits anything. A [`Declaration`] is the unit an artifact
//! carries and a choke point later re-checks; the checking, the audit, and the
//! environment that orders admissions belong to the crate above this one.

use alloc::vec::Vec;
use core::mem::ManuallyDrop;

use anodized::spec;
use gandr_kernel_strata::LandmarkConstraint;

use crate::arena::ArenaWatermark;
use crate::arena::TermArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::term::ConstantIndex;

/// The number of prenex level parameters a declaration binds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelParamCount(u32);

impl From<u32> for LevelParamCount
{
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<LevelParamCount> for u32
{
    #[inline]
    fn from(count: LevelParamCount) -> Self
    {
        count.0
    }
}

/// The admission position of one minted atom, as the artifact's minted-atom
/// table records it.
///
/// A bare index would be the wrong type here even though the representation is
/// the same integer: the table's entries are positions in an admission
/// sequence, and the reader compares them against positions it re-derived. The
/// wrapper is what stops one being crossed with a subterm-table index or a byte
/// offset at a signature.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MintedAtom(usize);

impl From<usize> for MintedAtom
{
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<MintedAtom> for usize
{
    #[inline]
    fn from(atom: MintedAtom) -> Self
    {
        atom.0
    }
}

/// A declaration's prenex level interface: how many level parameters it binds
/// and which landmark constraints it declares over them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LevelSignature
{
    /// The number of prenex level parameters.
    params: LevelParamCount,
    /// The declared landmark constraints, in declaration order.
    constraints: Vec<LandmarkConstraint>,
}

impl LevelSignature
{
    /// The signature of a declaration binding no level parameters.
    #[inline]
    #[must_use]
    pub fn monomorphic() -> Self
    {
        Self::default()
    }

    /// Pair a parameter count with the constraints declared over it.
    ///
    /// # Specification
    /// - requires: nothing — a constraint naming a parameter outside the count
    ///   is a rejection at the choke point rather than a construction error,
    ///   because the kernel grants the producer no credence about its own
    ///   signature.
    /// - ensures: the signature carries `params` and `constraints` verbatim, in
    ///   declaration order, which is the order the artifact writes them in.
    /// - provides: the level interface a declaration crosses the format with.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(captures: [entry_constraint_count = constraints.len()], ensures: |ret| ret.params() == params && ret.constraints().len() == entry_constraint_count)]
    pub fn new(
        params: LevelParamCount,
        constraints: Vec<LandmarkConstraint>,
    ) -> Self
    {
        Self {
            params,
            constraints,
        }
    }

    /// The number of prenex level parameters.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> LevelParamCount
    {
        self.params
    }

    /// The declared landmark constraints, in declaration order.
    #[inline]
    #[must_use]
    pub fn constraints(&self) -> &[LandmarkConstraint]
    {
        &self.constraints
    }
}

/// The content of a declaration: its roots into the arena that owns them.
///
/// The derived equality is child-id equality within one arena, never structural
/// equality across arenas; code needing agreement across arenas re-encodes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DeclarationContent
{
    /// A typed definition: a declared value type and a fully elaborated body,
    /// which a checker verifies against that type.
    Def
    {
        /// The declared value type's root id.
        declared: ValueTypeId,
        /// The elaborated value body's root id.
        body: ValueId,
    },
    /// A tracked typed hole: a declared value type with no body. Everything
    /// resting on it is what an audit reports.
    Axiom
    {
        /// The declared value type's root id.
        declared: ValueTypeId,
    },
    /// A sealed abstract type: a minted nominal atom, declared at a universe
    /// kind and with no unfolding rule.
    ///
    /// It is neither a definition nor a hole, and the distinction is the point.
    /// A definition carries a body a kernel must verify; an axiom claims an
    /// inhabitant and is therefore audited. An abstract type claims no
    /// inhabitant — it introduces an uninterpreted type constant, a
    /// conservative extension — so it is not audited as an axiom.
    AbstractType
    {
        /// The atom's kind: a universe value-type root id.
        kind: ValueTypeId,
    },
}

impl DeclarationContent
{
    /// The declared value-type root: the declared type of a definition or an
    /// axiom, and the kind of an abstract type.
    ///
    /// The three share one accessor because they share one well-formedness
    /// obligation — whatever the root is, it must form. What differs is what
    /// admission additionally demands of it, which is not this crate's plane.
    #[inline]
    #[must_use]
    pub const fn declared_id(&self) -> ValueTypeId
    {
        match *self {
            | Self::Def { declared, .. }
            | Self::Axiom { declared }
            | Self::AbstractType { kind: declared } => declared,
        }
    }
}

/// A declaration: a level interface, its content roots, and its sealing
/// provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Declaration
{
    /// The prenex level interface.
    levels: LevelSignature,
    /// The content roots, addressing the arena that minted them.
    content: DeclarationContent,
    /// The atoms this declaration's sealing projection rebound, as the
    /// artifact's sealing-provenance slot carries them.
    ///
    /// It records the projection, never the event. "This module was sealed" is
    /// a claim about an elaborator's history that a kernel would have to take
    /// on faith; "this declaration's type was projected onto these atoms"
    /// is a claim about *this declaration's type*, which a choke point
    /// re-derives by walking it. Empty for every declaration no projection
    /// touched.
    provenance: Vec<ConstantIndex>,
}

impl Declaration
{
    /// The prenex level interface.
    #[inline]
    #[must_use]
    pub const fn levels(&self) -> &LevelSignature
    {
        &self.levels
    }

    /// The content roots.
    #[inline]
    #[must_use]
    pub const fn content(&self) -> &DeclarationContent
    {
        &self.content
    }

    /// The declared value-type root.
    #[inline]
    #[must_use]
    pub const fn declared_id(&self) -> ValueTypeId
    {
        self.content.declared_id()
    }

    /// The atoms this declaration's projection rebound, in the order the
    /// artifact carries them.
    #[inline]
    #[must_use]
    pub fn provenance(&self) -> &[ConstantIndex]
    {
        &self.provenance
    }
}

/// How a declaration was admitted in the environment that produced it.
///
/// One bit, never a trust lattice: either the checked choke point admitted it
/// or a warned bypass did, and the artifact carries which so the audit survives
/// serialization.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AdmissionMark
{
    /// Admitted through the checked choke point.
    Checked,
    /// Admitted through the warned bypass.
    UncheckedBypass,
}

/// A declaration paired with the admission mark it carries on the wire.
///
/// This is the unit an artifact is a sequence of, in admission order, in both
/// directions: the encoder takes a slice of them and the decoder returns one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MarkedDeclaration
{
    /// How the producing environment admitted this declaration.
    mark: AdmissionMark,
    /// The declaration itself.
    declaration: Declaration,
}

impl MarkedDeclaration
{
    /// Pair an admission mark with a declaration.
    #[inline]
    #[must_use]
    pub const fn new(
        mark: AdmissionMark,
        declaration: Declaration,
    ) -> Self
    {
        Self { mark, declaration }
    }

    /// The admission mark.
    #[inline]
    #[must_use]
    pub const fn mark(&self) -> AdmissionMark
    {
        self.mark
    }

    /// The declaration, whose content roots address the arena beside it.
    #[inline]
    #[must_use]
    pub const fn declaration(&self) -> &Declaration
    {
        &self.declaration
    }
}

/// A borrowing builder for one declaration's content.
///
/// It lends the arena for minting the declared type and body, then finalizes a
/// [`Declaration`] over the roots that minting produced.
///
/// **Abandoning a builder rolls the arena back.** A builder dropped without
/// reaching a finisher — a scope exit on a failure path, or an explicit
/// [`Self::discard`] — truncates the arena to the watermark it recorded at
/// construction, so a lowering that fails partway leaves no orphan content
/// behind. A finisher consumes the builder without truncating: the minted
/// content becomes the declaration's.
///
/// # Specification
/// - requires: content for exactly one declaration is minted through
///   [`Self::arena`] between construction and a finisher, with no other
///   allocation into the arena interleaved — the recorded watermark and the
///   arena's end must describe a contiguous suffix.
/// - ensures: a finisher yields a [`Declaration`] over the minted roots and
///   leaves them in the arena; dropping the builder before a finisher restores
///   the arena to the recorded watermark.
/// - provides: the construction surface that ties content minting to the
///   watermark discipline, so the rollback is structural rather than a step a
///   failure path has to remember. This lifecycle contract stays prose: a
///   data-item `#[spec]` has no constructor-to-finisher or destructor
///   observation.
/// - fails: never — minting is total.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the rollback has one decision surface, separated by the
///   scope-exit abandonment, the explicit discard, and a finisher run, each
///   with the surviving arena content asserted exactly.
/// - witness: `decl::tests::an_abandoned_builder_restores_the_arena`
/// - witness: `decl::tests::a_discarded_builder_restores_the_arena`
/// - witness: `decl::tests::a_finished_builder_keeps_its_content`
pub struct DeclarationBuilder<'arena>
{
    /// The borrowed arena.
    arena: &'arena mut TermArena,
    /// The watermark at construction, which is where this content begins.
    content_start: ArenaWatermark,
}

impl<'arena> DeclarationBuilder<'arena>
{
    /// Begin building a declaration's content into `arena`, recording the
    /// content-start watermark.
    #[inline]
    #[must_use]
    pub fn new(arena: &'arena mut TermArena) -> Self
    {
        let content_start = arena.watermark();
        Self {
            arena,
            content_start,
        }
    }

    /// The watermark this content began at.
    #[inline]
    #[must_use]
    pub const fn content_start(&self) -> ArenaWatermark
    {
        self.content_start
    }

    /// The borrowed arena, for minting this declaration's content.
    #[inline]
    pub fn arena(&mut self) -> &mut TermArena
    {
        self.arena
    }

    /// Discard the staged content, restoring the arena to the content-start
    /// watermark.
    ///
    /// This is the explicit form of what the destructor does on scope exit;
    /// name it where the abandonment is the point of the path rather than the
    /// tail of an error return.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arena holds exactly the nodes it held at construction,
    ///   and every id minted through this builder dangles and is unreachable,
    ///   since no finisher ran and so no declaration roots it.
    /// - provides: the named abandonment path. Rollback stays prose: it occurs
    ///   when the consumed builder drops, after the attribute's normal-return
    ///   checks; no post-return arena borrow is available without changing this
    ///   signature.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub fn discard(self)
    {
        // Dropping `self` truncates the arena to the content-start watermark.
    }

    /// Finalize a definition over an already-minted declared type and body.
    #[inline]
    #[must_use]
    pub fn def(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        body: ValueId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Def { declared, body },
            provenance: Vec::new(),
        }
    }

    /// Finalize a definition carrying sealing provenance: the atoms the
    /// projection that produced its declared type rebound.
    ///
    /// # Specification
    /// - requires: nothing — a malformed provenance is a rejection at a choke
    ///   point, never a construction error, because the kernel grants the
    ///   producer no credence about what it sealed.
    /// - ensures: a declaration whose provenance slot carries `provenance`
    ///   verbatim, so admission checks exactly what the artifact would carry.
    /// - provides: the sealed-member construction surface.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(captures: [entry_provenance_count = provenance.len()], ensures: |ret| matches!(*ret.content(), DeclarationContent::Def { .. })
        && ret.provenance().len() == entry_provenance_count)]
    pub fn sealed_def(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        body: ValueId,
        provenance: Vec<ConstantIndex>,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Def { declared, body },
            provenance,
        }
    }

    /// Finalize an axiom over an already-minted declared type.
    #[inline]
    #[must_use]
    pub fn axiom(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Axiom { declared },
            provenance: Vec::new(),
        }
    }

    /// Finalize a sealed abstract type at an already-minted universe kind.
    ///
    /// # Specification
    /// - requires: nothing — a non-universe kind is a rejection at a choke
    ///   point, not a construction error.
    /// - ensures: a declaration whose content is an abstract type and whose
    ///   provenance is empty, an atom being what a projection produces rather
    ///   than something carrying a projection of its own.
    /// - provides: the atom-minting construction surface.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(*ret.content(), DeclarationContent::AbstractType { .. })
        && ret.provenance().is_empty())]
    pub fn abstract_type(
        self,
        levels: LevelSignature,
        kind: ValueTypeId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::AbstractType { kind },
            provenance: Vec::new(),
        }
    }
}

impl Drop for DeclarationBuilder<'_>
{
    /// Roll the arena back to the content-start watermark: a builder that never
    /// reached a finisher owns no content, so nothing it minted may survive it.
    #[inline]
    fn drop(&mut self)
    {
        self.arena.truncate_to(self.content_start);
    }
}

#[cfg(test)]
mod tests
{
    use super::DeclarationBuilder;
    use super::LevelSignature;
    use crate::arena::TermArena;

    #[test]
    fn an_abandoned_builder_restores_the_arena()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let staged = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            builder.arena().value_unit()
        };
        assert_eq!(
            before,
            arena.watermark(),
            "a builder dropped at scope exit restores the watermark"
        );
        assert!(
            arena.value(staged).is_none(),
            "content staged by an abandoned builder is gone"
        );
    }

    #[test]
    fn a_discarded_builder_restores_the_arena()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let staged = builder.arena().value_unit();
        builder.discard();
        assert_eq!(
            before,
            arena.watermark(),
            "an explicitly discarded builder restores the watermark"
        );
        assert!(
            arena.value(staged).is_none(),
            "content staged by a discarded builder is gone"
        );
    }

    #[test]
    fn a_finished_builder_keeps_its_content()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let mut builder = DeclarationBuilder::new(&mut arena);
        assert_eq!(
            before,
            builder.content_start(),
            "the builder records the watermark it began at"
        );
        let declared = builder.arena().value_type_unit();
        let body = builder.arena().value_unit();
        let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
        assert_ne!(
            before,
            arena.watermark(),
            "a finisher leaves the minted content in the arena"
        );
        assert!(
            arena.value(body).is_some(),
            "the finished declaration's body still resolves"
        );
        assert_eq!(
            declared,
            declaration.declared_id(),
            "the declared root is kept"
        );
        assert!(
            declaration.provenance().is_empty(),
            "an ordinary definition carries no sealing provenance"
        );
    }
}
