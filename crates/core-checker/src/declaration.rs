//! The name-free declaration input: what one declaration offers the judgement.
//!
//! # Name-free, and owned here
//!
//! A [`Declaration`] carries an admission position, an optional declared type,
//! an optional body and an [`OriginToken`]. It carries no name, no span and no
//! syntax node: the producer of the terms resolves names to positions and keeps
//! the origins, and the checker echoes the token back beside every verdict so
//! the driver can resolve it. This crate owns the type; a producer is adapted
//! to it downstream of both, so the two never agree on more than this one small
//! shape.
//!
//! # Each half is present or absent for a stated reason
//!
//! A missing declared type means the author wrote a definition with no
//! signature, so the body must synthesise. A missing body is a hole: no
//! definition supplies it. Both halves are independent, so the hole's rule is
//! read in both directions — under a signature it absorbs the declared type
//! and owes it, and with no signature it is refused, because nothing hands it a
//! type.
//!
//! A [`DeclarationContent`] distinguishes the optional value halves from a
//! complete native `DataSignature` and from a sealed [`AbstractType`]. Reading
//! a lowering's outcome type directly would couple independent layers; the
//! adapter is revisited only if a shared producer-neutral declaration
//! vocabulary replaces it. Names enter only at export, through
//! `bridge::Readmission::export`.
//!
//! # A sealed abstract type
//!
//! Opaque ascription declares each abstract component as an atom at its own
//! admission position, before the members that implement it: its kind, its
//! representation, how many positions after it stay inside the seal, and the
//! site that minted it. The atom's identity is the position; the extent says
//! where the representation stops being visible, so the module's own members
//! check at the representation and every later declaration sees the atom
//! alone.

use anodized::spec;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SealExtent;
use quenchant_shape::shape::Maybe;

use crate::seal::SealSite;

quenchant_shape::reason_enum! {
    /// Why a declaration carries no declared type.
    pub mod signature {
        /// The reason the declared type is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The author wrote a definition and no signature, so the body
            /// must synthesise its own type.
            Unsigned,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration carries no body.
    pub mod body {
        /// The reason the body is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The body is a hole: no definition supplies it.
            Hole,
        }
    }
}

/// The opaque handle a producer attaches to a declaration, echoed back with its
/// verdict.
///
/// The checker never interprets the index it wraps; the driver resolves it to
/// the declaration's name and span through whatever table issued it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OriginToken(usize);

impl From<usize> for OriginToken
{
    /// The token wrapping `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<OriginToken> for usize
{
    /// The index `token` wraps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(token: OriginToken) -> Self
    {
        token.0
    }
}

/// A sealed abstract type: an atom of a universe, the representation it
/// stands for inside its seal, and the reach of that seal.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AbstractType
{
    /// The universe the atom inhabits.
    kind: ValueTypeId,
    /// The type the atom stands for inside its seal.
    representation: ValueTypeId,
    /// How many admission positions after the atom's own stay inside the
    /// seal.
    extent: SealExtent,
    /// The sealing site that mints the atom.
    site: SealSite,
}

impl AbstractType
{
    /// The atom of `kind` standing for `representation` for the `extent`
    /// positions after its own, minted at `site`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        kind: ValueTypeId,
        representation: ValueTypeId,
        extent: SealExtent,
        site: SealSite,
    ) -> Self
    {
        Self {
            kind,
            representation,
            extent,
            site,
        }
    }

    /// The universe the atom inhabits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> ValueTypeId
    {
        self.kind
    }

    /// The type the atom stands for inside its seal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn representation(&self) -> ValueTypeId
    {
        self.representation
    }

    /// How many admission positions after the atom's own stay inside the
    /// seal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn extent(&self) -> SealExtent
    {
        self.extent
    }

    /// The sealing site that mints the atom.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn site(&self) -> SealSite
    {
        self.site
    }
}

/// The three disjoint declaration judgments.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum DeclarationContent
{
    /// An optionally ascribed value or an explicit hole.
    Value
    {
        /// The declared value type, if any.
        signature: Maybe<ValueTypeId, signature::Absent>,
        /// The defining value, or an explicit hole.
        body: Maybe<ValueId, body::Absent>,
    },
    /// A native nominal signature; it is neither a value body nor a hole.
    Data(alloc::sync::Arc<gandr_core_term::DataSignature>),
    /// A sealed abstract type; an atom, neither a value nor an assumption.
    Abstract(AbstractType),
}
/// One declaration, as the judgement reads it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Declaration
{
    /// The admission position the declaration takes.
    constant: ConstantIndex,
    /// The value declaration or native nominal signature.
    content: DeclarationContent,
    /// The producer's handle, echoed back.
    origin: OriginToken,
}

impl Declaration
{
    /// The declaration at `constant` with these halves and this origin.
    ///
    /// # Specification
    /// - requires: nothing; judgement checks arena membership and admission
    ///   order rather than trusting the producer.
    /// - ensures: the accessors return exactly the arguments.
    /// - provides: the one constructor; every combination of present and absent
    ///   halves is representable, the body-less, signature-less one included,
    ///   because the hole rule answers it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over all four combinations of declaration halves,
    ///   module verdicts distinguish checking, synthesis and the two hole
    ///   directions; their origins separate lost provenance. Arena membership
    ///   and admission order are obligations of judgement, not construction.
    /// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
    /// - witness: `module::tests::an_admission_out_of_order_is_refused`
    #[spec(ensures: |ret| ret.constant == constant && ret.origin == origin
        && matches!(ret.content, DeclarationContent::Value { signature: declared, body: defined } if declared == signature && defined == body))]
    #[inline]
    #[must_use]
    pub fn new(
        constant: ConstantIndex,
        signature: Maybe<ValueTypeId, signature::Absent>,
        body: Maybe<ValueId, body::Absent>,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            content: DeclarationContent::Value { signature, body },
            origin,
        }
    }

    /// The admission position the declaration takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The value declaration or native nominal signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn content(&self) -> &DeclarationContent
    {
        &self.content
    }

    /// A nominal declaration at its own admission position.
    ///
    /// The shared immutable signature is retained by the declaration, context
    /// and report without copying its parameter and constructor telescopes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn data(
        constant: ConstantIndex,
        signature: alloc::sync::Arc<gandr_core_term::DataSignature>,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            origin,
            content: DeclarationContent::Data(signature),
        }
    }

    /// A sealed abstract type at its own admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn abstract_type(
        constant: ConstantIndex,
        sealed: AbstractType,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            origin,
            content: DeclarationContent::Abstract(sealed),
        }
    }

    /// The producer's handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.origin
    }
}
