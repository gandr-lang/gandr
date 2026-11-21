//! How a verdict names a node of the core: by its id in one arena, or by its
//! content key.
//!
//! The checker judges over one arena, and its verdicts name each node by its
//! arena id. A report that outlives the judgement names each node by its
//! content key. Two sessions that judge one text mint their nodes in different
//! orders, but they agree on each key. The verdict and its refusals are generic
//! over the naming. The `keyed` map of each takes the arena form to the keyed
//! form, and the arena form never reaches a report.

use core::fmt::Debug;
use core::hash::Hash;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::key::NodeKey;

use crate::formation::FormedValueType;

/// A naming of the core's nodes: the type that names each family of nodes.
///
/// A naming is a marker type with no value. It derives each trait that a
/// verdict derives, so that a verdict generic over its naming derives them too.
///
/// # Specification
/// - executable: none — a trait of types; [`Arena`] and [`Keyed`] are its
///   namings.
pub trait Naming: Copy + Debug + Eq + Hash + Ord
{
    /// The name of a value node.
    type Value: Copy + Debug + Eq + Hash + Ord;
    /// The name of a computation node.
    type Computation: Copy + Debug + Eq + Hash + Ord;
    /// The name of a value-type node.
    type ValueType: Copy + Debug + Eq + Hash + Ord;
    /// The name of a computation-type node.
    type CompType: Copy + Debug + Eq + Hash + Ord;
    /// The name of a value type that a rule formed.
    type Formed: Copy + Debug + Eq + Hash + Ord;
}

/// The naming of the checker: each node by its id in the arena that it judges
/// over.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arena;

impl Naming for Arena
{
    type CompType = CompTypeId;
    type Computation = ComputationId;
    type Formed = FormedValueType;
    type Value = ValueId;
    type ValueType = ValueTypeId;
}

/// The naming of a report: each node by its content key.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Keyed;

impl Naming for Keyed
{
    type CompType = NodeKey;
    type Computation = NodeKey;
    type Formed = NodeKey;
    type Value = NodeKey;
    type ValueType = NodeKey;
}

/// The content key of each node of one arena, which the `keyed` maps read.
///
/// # Specification
/// - executable: none — a trait; the composition implements it over the arena
///   that it judges over.
pub trait Keying
{
    /// The content key of the value node `value`.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &self,
        value: ValueId,
    ) -> NodeKey;

    /// The content key of the computation node `computation`.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &self,
        computation: ComputationId,
    ) -> NodeKey;

    /// The content key of the value-type node `value_type`.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &self,
        value_type: ValueTypeId,
    ) -> NodeKey;

    /// The content key of the computation-type node `comp_type`.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &self,
        comp_type: CompTypeId,
    ) -> NodeKey;

    /// The content key of the formed value type `formed`: the key of its node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn formed(
        &self,
        formed: FormedValueType,
    ) -> NodeKey
    {
        self.value_type(formed.id())
    }
}
