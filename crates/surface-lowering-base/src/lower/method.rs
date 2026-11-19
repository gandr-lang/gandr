//! The records of the method calls that the lowering's context holds.
//!
//! The classification reads a method call, what it does with its receiver and
//! the place a view method answers into these records. The mint sweep reads
//! them back, and `gandr-surface-lowering` names each one at its old path.

use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use crate::by_form::FormStretch;
use crate::resolve::ScopeId;

/// What a method call does with its receiver.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each held slot is a linear index where the call stands.
/// - executable: none — the plan holds no scope to resolve its indices in.
///
/// # Adequacy
/// - hypothesis: L3 — a call at each mode on a held receiver, and on one that
///   is not held.
/// - witness: `gandr-surface-lowering::lower::method::tests::each_mode_lowers_to_its_access`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Receiving
{
    /// The held slot read through a shared view.
    Read
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
    },
    /// The held slot written through an exclusive view.
    Written
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
    },
    /// The held slot taken, ending its hold.
    Taken
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
    },
    /// A receiver that is no held slot, read as a value where the call stands
    /// and passed as the first argument.
    Passed,
    /// The held slot's place the method answers, its index read through a
    /// shared view, lent to the call's block or read without one.
    Viewed
    {
        /// The slot, a linear index.
        held: DeBruijnIndex,
        /// The block the place is lent to.
        view: Maybe<ViewBlock, unviewed::Absent>,
    },
}

/// The block a call of a method answering a place lends the place to, `s.f(a)
/// as w { b }`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `body` reads under `binder`, the view `w`'s linear binder over
///   the index's; `call` is the call `s.f(a)` the block follows.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a block that ends its view and one that reads it.
/// - witness: `gandr-surface-lowering::lower::method::tests::a_view_block_lends_at_the_mode_it_asks`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ViewBlock
{
    /// The view's binder, which a `resume` or `abort` in the block ends.
    pub binder: ScopeId,
    /// The block.
    pub body: Block,
    /// The call the block follows, whose own application stands there.
    pub call: NodeIndex,
}

quenchant_shape::reason_enum! {
    /// Why a call of a method answering a place lends it to no block.
    pub mod unviewed {
        /// The call has no block.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The call stands alone, reading its place.
            Read,
        }
    }
}

/// The place a method answering a view ends in, `self.#[e]`.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `element` is the view's element type `a` of the method's result
///   `-F View[m](a)`, read as a value type past every parameter.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a method answering its receiver's first element.
/// - witness: `gandr-surface-lowering::lower::method::tests::a_view_method_answers_its_place_index`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct ViewPlace
{
    /// The view's element type.
    pub element: NodeIndex,
}

/// A method call, as the classification read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the arguments read under the binder the receiving opens: a view's
///   for a read or a write, the taken value's for a take; `head` is the call's
///   head `s.f` and `receiver` its `s`.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Receiving`].
/// - witness: `gandr-surface-lowering::lower::method::tests::each_mode_lowers_to_its_access`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Called
{
    /// The method's constant.
    pub method: ConstantIndex,
    /// What the call does with its receiver.
    pub receiving: Receiving,
    /// The arguments after the receiver, in the lowerer's operand store.
    pub arguments: FormStretch,
    /// The call's head, `s.f`, which answers with the method.
    pub head: NodeIndex,
    /// The receiver `s`, which answers with the value the method receives.
    pub receiver: NodeIndex,
}

/// The receiver a written-through method's body holds.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `position` indexes the function's parameters and `index` is that
///   parameter's intuitionistic index past every parameter.
/// - executable: none — the plan holds no scope.
///
/// # Adequacy
/// - hypothesis: L3 — a written-through method's body and its declared result.
/// - witness: `gandr-surface-lowering::lower::method::tests::a_written_through_body_returns_its_receiver`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HeldReceiver
{
    /// The receiver's place among the function's parameters.
    pub position: usize,
    /// The receiver parameter's intuitionistic index past every parameter.
    pub index: DeBruijnIndex,
}

quenchant_shape::reason_enum! {
    /// Why a function holds no receiver over its body.
    pub mod unheld {
        /// The function holds no receiver.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The function is no method, or its method reads or takes its
            /// receiver.
            NotWrittenThrough,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an instantiation is not a bare index.
    pub mod unindexing {
        /// The bracket of the instantiation holds static arguments.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head is not a bare name.
            Unnamed,
            /// The bracket holds a termination claim, `<` or `>`.
            Claimed,
            /// The name resolves to no binder. Or it resolves to the binder
            /// of a recursive function, which a claim instantiates.
            Static,
        }
    }
}
