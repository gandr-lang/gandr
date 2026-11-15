//! The records of the loops that the lowering's context holds.
//!
//! The classification reads what a loop threads through its passes and where
//! a pass runs the loop again into these records. The mint sweep reads them
//! back, and `gandr-surface-lowering` names each one at its old path.

use gandr_core_term::ComponentCount;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

/// What a loop threads through its passes: a held slot, held again in each
/// pass, or an endpoint, placed again in each pass.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Carry
{
    /// A held slot.
    Held,
    /// An endpoint.
    Endpoint,
}

/// Where a pass through a loop's body runs the loop again from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Reentry
{
    /// The index the loop's own binder has.
    pub own: DeBruijnIndex,
    /// The index a `for` loop's remaining tail has, which the next pass steps
    /// through.
    pub tail: Maybe<DeBruijnIndex, passed::Absent>,
    /// The held slots the next pass takes, when the loop threads any.
    pub carried: Maybe<Carried, carried::Absent>,
}

quenchant_shape::reason_enum! {
    /// Why a loop's next pass steps through no tail.
    pub mod passed {
        /// The loop iterates no list.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A `loop` or a `while` runs its next pass over nothing.
            Unlisted,
        }
    }
}

/// The held slots a pass hands the loop's next pass, where the pass stands:
/// the innermost slot's linear index and how many slots there are, each next
/// one a linear index further out.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Carried
{
    /// The linear index the innermost slot has.
    pub innermost: DeBruijnIndex,
    /// How many slots the loop threads.
    pub count: ComponentCount,
}

quenchant_shape::reason_enum! {
    /// Why a loop's next pass takes no held slot.
    pub mod carried {
        /// The loop threads none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No slot held around the loop is named inside it, or the loop
            /// stands where it cannot thread one.
            Unthreaded,
        }
    }
}
