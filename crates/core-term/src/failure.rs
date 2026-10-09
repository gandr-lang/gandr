//! The four classes every refusal of the core pipeline answers to.
//!
//! # Whose fact a failure is, decided by a type
//!
//! A refusal records whose fact a failure is: an absence the author has not
//! supplied yet, a form the engine cannot represent, a form the author wrote
//! wrongly, or a fault of the engine's own or of its caller. The split is
//! sharper than a three-way one, because an author-written form the engine
//! declines to represent is a different fact from an author-written form that
//! is simply wrong, and only the first says anything about the fragment's
//! reach.
//!
//! # One vocabulary below every producer
//!
//! The lowering and the checker each classify their own refusals, and a report
//! groups both under one set of classes. The classes therefore live in the one
//! crate both depend on, so neither names the other and there is one enum
//! rather than two that agree by convention. Each producer's classifier is its
//! own `const`, wildcard-free match over its own refusals.

use core::fmt;

/// Whose fact a refusal records.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FailureClass
{
    /// The author has not supplied it yet: reportable as a ledger entry, and
    /// the only class that may become an obligation.
    UserAbsence,
    /// The engine cannot represent what the author wrote.
    Unrepresentable,
    /// The author wrote it and it is wrong.
    MalformedSource,
    /// The engine failed for reasons of its own or its caller's.
    EngineFault,
}

impl fmt::Display for FailureClass
{
    /// Writes the class's name.
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
            | Self::UserAbsence => f.write_str("user absence"),
            | Self::Unrepresentable => f.write_str("unrepresentable"),
            | Self::MalformedSource => f.write_str("malformed source"),
            | Self::EngineFault => f.write_str("engine fault"),
        }
    }
}
