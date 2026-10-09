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

use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

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

/// One declaration, as the judgement reads it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Declaration
{
    /// The admission position the declaration takes.
    constant: ConstantIndex,
    /// The declared type, or why there is none.
    signature: Maybe<ValueTypeId, signature::Absent>,
    /// The body, or why there is none.
    body: Maybe<ValueId, body::Absent>,
    /// The producer's handle, echoed back.
    origin: OriginToken,
}

impl Declaration
{
    /// The declaration at `constant` with these halves and this origin.
    ///
    /// # Specification
    /// - requires: every id resolves in the arena the checking context reads,
    ///   and `constant` is above every position already offered to that
    ///   context; the checker refuses either breach rather than trusting it.
    /// - ensures: the accessors return exactly the arguments.
    /// - provides: the one constructor; every combination of present and absent
    ///   halves is representable, the body-less, signature-less one included,
    ///   because the hole rule answers it.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new(
        constant: ConstantIndex,
        signature: Maybe<ValueTypeId, signature::Absent>,
        body: Maybe<ValueId, body::Absent>,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            signature,
            body,
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

    /// The declared type, or why there is none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn signature(&self) -> Maybe<ValueTypeId, signature::Absent>
    {
        self.signature
    }

    /// The body, or why there is none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn body(&self) -> Maybe<ValueId, body::Absent>
    {
        self.body
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
