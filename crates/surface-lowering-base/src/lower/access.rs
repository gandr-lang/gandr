//! The records of temporary access that the lowering's context holds.
//!
//! The classification reads a hold, an access, an eliminator of a view and a
//! place assignment into these records. The mint sweep reads them back, and
//! `gandr-surface-lowering` names each one at its old path.

use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Primitive;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use crate::form::TileName;

/// A temporary-access form, as the classification read it.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each index names a linear binder where the form stands; an
///   access's body reads under the view's binder and its unwind where the
///   access stands.
/// - executable: none — the plan holds no scope to resolve its indices in.
///
/// # Adequacy
/// - hypothesis: L3 — the counter's hold, both accesses and both eliminators
///   lower to the core forms they name.
/// - witness: `gandr-surface-lowering::lower::access::tests::the_counter_lowers_to_its_memory_forms`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Accessed
{
    /// `access x as v { t } unwind { u }` or `access shared x as v { t }`,
    /// either of a place `x.#[e]`.
    Access
    {
        /// The mode the slot is lent in, with an exclusive access's unwind
        /// when one is written.
        mode: AccessMode<Maybe<Block, unwound::Absent>>,
        /// The held slot lent, a linear index where the access stands.
        held: DeBruijnIndex,
        /// The place of the held value lent, its index read where the access
        /// stands.
        place: Place<NodeIndex>,
        /// The body, under the view's linear binder.
        body: Block,
    },
    /// `resume v e`.
    Resume
    {
        /// The view ended, a linear index.
        view: DeBruijnIndex,
        /// The value written back.
        value: NodeIndex,
    },
    /// `abort v`.
    Abort
    {
        /// The view ended, a linear index.
        view: DeBruijnIndex,
    },
    /// The place `self.#[e]` a method answering a view ends in: its receiver
    /// held and lent shared at `e`, the view judged at the element type, and
    /// the index answered.
    Place
    {
        /// The receiver, an intuitionistic index where the place stands.
        receiver: DeBruijnIndex,
        /// The index `e`, read as a value where the place stands.
        index: NodeIndex,
        /// The element type the method's result names, read as a value type
        /// where the place stands.
        element: NodeIndex,
    },
    /// A bare index `s.#[e]` of a held slot: the element at `e`, read through a
    /// shared view of it that answers what it views.
    Element
    {
        /// The held slot lent, a linear index where the index stands.
        held: DeBruijnIndex,
        /// The index `e`, read as a value where the index stands.
        index: NodeIndex,
    },
    /// A bare index `e.#[i]` of a list no hold holds: the list held for the
    /// read alone, lent shared at `i`, and the element its view sees answered.
    Unheld
    {
        /// The list `e`, read as a value where the index stands.
        list: NodeIndex,
        /// The index `i`, read as a value where the index stands.
        index: NodeIndex,
    },
    /// A place assignment `p = e ;`, or `p += e ;` with the operator's row:
    /// `e`'s value bound first, then the place lent exclusively and written
    /// that value, or the row over the view and that value.
    Assign
    {
        /// The held slot written, a linear index where the statement stands.
        held: DeBruijnIndex,
        /// The place of the held value written, its index read where the
        /// statement stands.
        place: Place<NodeIndex>,
        /// The right side, read as a value where the statement stands.
        value: NodeIndex,
        /// The row a compound assignment applies to the view and the right
        /// side's value.
        combined: Maybe<Primitive, assigned::Absent>,
    },
}

/// A place assignment a block read, by its place's node.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `operator` is the assignment's tile, `=`, `+=`, `-=` or `*=`;
///   `value` is read as a value where the statement stands.
/// - executable: none — the record names nodes the classification reads.
///
/// # Adequacy
/// - hypothesis: L3 — a plain and a compound assignment each lower to the
///   access they write.
/// - witness: `gandr-surface-lowering::lower::access::tests::a_place_assignment_writes_through_an_exclusive_view`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Assignment
{
    /// The operator tile written after the place.
    pub operator: TileName,
    /// The right side.
    pub value: NodeIndex,
}

quenchant_shape::reason_enum! {
    /// Why a `var` states no type.
    pub mod unstated {
        /// The statement writes no `: T` after its name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The held value's type is the checker's to read off it.
            Unwritten,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an assignment applies no operator's row.
    pub mod assigned {
        /// The assignment is written `=`.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The place is written the right side's value itself.
            Plain,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an access has no unwind block.
    pub mod unwound {
        /// The access holds no `unwind` clause.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No unwind was written; the access unwinds by `pure unit`.
            Unwritten,
        }
    }
}
