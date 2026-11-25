//! The records of the prelude's binary naturals that the lowering's context
//! holds.
//!
//! A numeral annotated at the prelude's `Nat` mints the constructors these
//! records name. `gandr-surface-lowering` names each one at its old path.

use gandr_core_term::ConstructorTag;
use gandr_kernel_term::ConstantIndex;

/// A constructor as the mint reads it: its family's admission position and
/// its tag.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Generator
{
    /// The family's admission position.
    pub family: ConstantIndex,
    /// The constructor's tag.
    pub tag: ConstructorTag,
}

/// The prelude's binary naturals: `Nat`'s admission position and the five
/// constructors a numeral at `Nat` mints.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each field is the prelude's declaration of its name.
/// - executable: none — positions into a module this record does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one and a numeral of several digits each mint the
///   prelude's constructors.
/// - witness: `gandr-surface-lowering::lower::natural::tests::a_numeral_at_nat_is_its_binary_constructor_term_3287`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Naturals
{
    /// `Nat`.
    pub nat: ConstantIndex,
    /// `Zero`.
    pub zero: Generator,
    /// `Positive`.
    pub positive: Generator,
    /// `One`.
    pub one: Generator,
    /// `Bit0`.
    pub bit0: Generator,
    /// `Bit1`.
    pub bit1: Generator,
}
