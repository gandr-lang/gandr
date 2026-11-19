//! The records of a derived equality that the lowering's context holds.
//!
//! The classification reads a definition written `Eq.generic(T)` or one of its
//! laws into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use gandr_core_term::generic::law::Statement;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::ByteSpan;

use crate::form::Placed;
use crate::resolve::SurfaceName;

/// What a definition written as the derivation's call derives.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Derivation
{
    /// `Eq.generic(T)`: the equality.
    Equality,
    /// `Eq.generic.refl(T)` or `Eq.generic.sym(T)`: a law of the equality.
    Law(Statement),
}

/// One definition written `Eq.generic(T)`, `Eq.generic.refl(T)` or
/// `Eq.generic.sym(T)`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Requested<'source>
{
    /// What it derives.
    pub derivation: Derivation,
    /// The data declaration `T` names.
    pub data: ConstantIndex,
    /// Where `T` is written.
    pub named: ByteSpan,
    /// `T` as written.
    pub name: SurfaceName<'source>,
    /// The call itself, where the derived body is located.
    pub call: Placed,
}
