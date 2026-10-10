//! Canonical content: an item's or a type's nodes as a table numbered by
//! discovery, free of arena ids and admission positions.
//!
//! # One table per item, numbered by discovery
//!
//! An item's content is every node reachable from its signature and its body,
//! each listed once, numbered in the order a breadth-first walk from the two
//! roots first discovers it, children left to right. A child is named by its
//! number, a constant by the [`Reference`] its position resolves to. Two
//! items built in two arenas, with different ids, have equal tables exactly
//! when their node graphs are the same graph with the same sharing: sharing
//! that differs makes the tables differ, which costs a reuse and never a wrong
//! answer. The walk visits each node once, so the table is linear in the
//! item's distinct nodes whatever its sharing, and it needs no stack: the
//! queue holds the frontier, and a node is written when it leaves the queue,
//! by which time every child already has its number.
//!
//! # An id the arena does not hold
//!
//! An id that resolves to nothing is a fact about another arena. It is listed
//! as [`ContentNode::Unresolved`] with its sort, so encoding stays total, and
//! a table holding one is opaque: its item is never adopted and never
//! persisted.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use quenchant_shape::shape::Maybe;

use crate::boundary::NodeIndex;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;

quenchant_shape::reason_enum! {
    /// Why a type table could not be minted back into an arena.
    pub mod seating {
        /// The reason no node was minted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The table holds an id another arena minted.
            Unresolved,
            /// The table holds a node that is its own descendant, which no
            /// arena can mint child before parent.
            Cyclic,
            /// The table names an item the program does not hold.
            Unplaced,
            /// The table is not a value type, or a child has the wrong sort.
            IllSorted,
            /// The type holds a term — the code of an element type — and a
            /// seat mints types alone.
            Unseatable,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an arena node has no site in an item's table.
    pub mod site {
        /// The reason no site is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The item's walk never reached the node.
            Unreached,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a content node names no reference.
    pub mod referencing {
        /// The reason no reference is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node is neither a constant nor an abstract type.
            NotAReference,
        }
    }
}

/// The four node sorts of the core vocabulary.
///
/// # Specification
/// - executable: none — a sort tag carries no arena or node whose
///   classification it could certify.
///
/// # Adequacy
/// - hypothesis: L2 — the finite content corpus exercises all four sorts; the
///   tag alone does not certify a table edge.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sort
{
    /// A value.
    Value,
    /// A computation.
    Computation,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
}

/// A node of a core arena, of any sort.
///
/// # Specification
/// - executable: none — the tagged identifier has no arena to establish whether
///   its node resolves.
///
/// # Adequacy
/// - hypothesis: L2 — arena-relative identity is separated by allocation noise
///   and an unresolved value identifier; other unresolved sorts are not claimed
///   here.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ArenaNode
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
    /// A value-type node.
    ValueType(ValueTypeId),
    /// A computation-type node.
    CompType(CompTypeId),
}

/// One node of a content table: a core former over table indices.
///
/// # Specification
/// - executable: none — an entry alone has neither its table nor its arena;
///   edge validity belongs to the consuming walk.
///
/// # Adequacy
/// - hypothesis: L3 — shared and unresolved nodes, interleaved roots and the
///   finite persistence corpus bound the former and edge evidence; raw entries
///   need not form a closed or well-sorted table.
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ContentNode
{
    /// A closed table-typed native thunk.
    PrimitiveValue(gandr_core_term::primitive::Primitive),
    /// A saturated runtime-native operation.
    Primitive(
        gandr_core_term::primitive::Primitive,
        gandr_core_term::primitive::Arguments<NodeIndex>,
    ),
    /// A native universe-path classifier over quoted codes.
    PathUniverse(NodeIndex, NodeIndex),
    /// A reflexivity certificate.
    PathRefl(NodeIndex),
    /// A product certificate.
    PathProduct(NodeIndex, NodeIndex),
    /// An equivalence, retaining its evidence in the cache identity.
    PathEquiv
    {
        /// The classifier.
        path_type: NodeIndex,
        /// The forward map.
        forward: NodeIndex,
        /// The inverse map.
        backward: NodeIndex,
        /// The untrusted round-trip dialogues.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// Native transport.
    Transport(NodeIndex, NodeIndex),
    /// A bound variable.
    Variable
    {
        /// The zone its index counts in.
        zone: Zone,
        /// The index.
        index: DeBruijnIndex,
    },
    /// A constant, by what its position names.
    Constant(Reference),
    /// The unit value.
    Unit,
    /// A literal.
    Literal(Literal),
    /// A pair of values.
    Pair(NodeIndex, NodeIndex),
    /// A sum injection.
    Injection(Side, NodeIndex),
    /// A thunk of a computation.
    Thunk(NodeIndex),
    /// A universe lift of a value.
    ValueLift
    {
        /// The target level.
        target: Level,
        /// The value lifted.
        body: NodeIndex,
    },
    /// The code of a value type.
    Quote(NodeIndex),
    /// The code of a computation type.
    QuoteComputation(NodeIndex),
    /// A static lambda over its body, under one binder.
    StaticLambda(NodeIndex),
    /// A static application of an operator to an argument.
    StaticApplication(NodeIndex, NodeIndex),
    /// A lambda over its body.
    Lambda(NodeIndex),
    /// An application of a computation to a value.
    Application(NodeIndex, NodeIndex),
    /// A return of a value.
    Return(NodeIndex),
    /// A bind of a computation into a continuation.
    Bind(NodeIndex, NodeIndex),
    /// A force of a value.
    Force(NodeIndex),
    /// A sum elimination.
    Case
    {
        /// The scrutinee.
        scrutinee: NodeIndex,
        /// The left branch.
        on_left: NodeIndex,
        /// The right branch.
        on_right: NodeIndex,
    },
    /// A base-type atom.
    Base(BaseType),
    /// The unit type.
    UnitType,
    /// A product type.
    Product(NodeIndex, NodeIndex),
    /// A sum type.
    Sum(NodeIndex, NodeIndex),
    /// A thunk type.
    ThunkType(NodeIndex),
    /// A universe of one sort.
    Universe
    {
        /// The family it classifies.
        sort: gandr_core_term::Sort,
        /// Its level within that family.
        level: Level,
    },
    /// A lift of a value type.
    TypeLift
    {
        /// The type lifted.
        inner: NodeIndex,
        /// The target level.
        target: Level,
    },
    /// The type a code denotes.
    Element
    {
        /// The code.
        code: NodeIndex,
        /// The level it is read at.
        target: Level,
    },
    /// A static Pi, whose codomain binds nothing.
    StaticPi
    {
        /// The domain.
        domain: NodeIndex,
        /// The codomain.
        codomain: NodeIndex,
    },
    /// A sealed abstract type, by what its position names.
    Abstract(Reference),
    /// A returner type.
    Returner(NodeIndex),
    /// A non-dependent arrow.
    Arrow
    {
        /// The domain.
        domain: NodeIndex,
        /// The codomain.
        codomain: NodeIndex,
    },
    /// A dependent arrow.
    Pi
    {
        /// The domain.
        domain: NodeIndex,
        /// The codomain, under the domain's binder.
        codomain: NodeIndex,
    },
    /// The computation type a code denotes.
    ComputationElement
    {
        /// The code.
        code: NodeIndex,
        /// The level it is read at.
        target: Level,
    },
    /// An id of this sort the arena resolves to nothing.
    Unresolved(Sort),
}

/// The children of one content node, each with the sort it must have.
///
/// # Specification
/// - executable: none — the active-prefix representation is maintained by
///   `Children::of` and read by the graph walks, not a callable declaration.
///
/// # Adequacy
/// - hypothesis: L2 — sharing and interleaved roots exercise active child
///   slots; the persistence corpus covers selected multi-sort formers, not
///   every graph.
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Children
{
    /// The children in order; slots past `count` are unused.
    slots: [(NodeIndex, Sort); 3],
    /// How many slots hold a child.
    count: usize,
}

impl Default for Sort
{
    /// The value sort, which only fills unused child slots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::Value
    }
}

impl Children
{
    /// The children listed in `children`, in order.
    ///
    /// # Specification
    /// - requires: at most three children, which every former satisfies.
    /// - ensures: the first `children.len()` slots, in order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — shared nodes and the signature walk exercise active
    ///   child slots through graph consumers; the finite corpus adds selected
    ///   arities.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(
        requires: children.len() <= 3,
        ensures: |ret| ret.count == children.len()
            && ret.slots.get(..ret.count) == Some(children),
    )]
    fn of(children: &[(NodeIndex, Sort)]) -> Self
    {
        let mut slots = [(NodeIndex::default(), Sort::Value); 3];
        let mut count = 0_usize;
        for (slot, &child) in slots.iter_mut().zip(children) {
            *slot = child;
            count = count.saturating_add(1);
        }
        Self { slots, count }
    }

    /// The children, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the active prefix, in order, excluding unused slots.
    /// - executable: none — anodized 0.7 emits an invalid closure return type
    ///   for this opaque iterator, including for preconditions alone.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named graph consumer exercises the iterator; that
    ///   bounded evidence does not instrument the opaque return.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    pub(crate) fn iter(&self) -> impl Iterator<Item = (NodeIndex, Sort)> + '_
    {
        self.slots.iter().copied().take(self.count)
    }
}

impl ContentNode
{
    /// The node's sort.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the core family of the former, or the stored unresolved sort.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises all four
    ///   families; the unresolved witness bounds the foreign-identifier case to
    ///   values.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| match *self {
        | Self::PathRefl(_)
        | Self::PrimitiveValue(_)
        | Self::PathProduct(..)
        | Self::PathEquiv { .. }
        | Self::Variable { .. }
        | Self::Constant(_)
        | Self::Unit
        | Self::Literal(_)
        | Self::Pair(..)
        | Self::Injection(..)
        | Self::Thunk(_)
        | Self::ValueLift { .. }
        | Self::Quote(_)
        | Self::QuoteComputation(_)
        | Self::StaticLambda(_)
        | Self::StaticApplication(..) => matches!(ret, Sort::Value),
        | Self::Transport(..)
        | Self::Primitive(..)
        | Self::Lambda(_)
        | Self::Application(..)
        | Self::Return(_)
        | Self::Bind(..)
        | Self::Force(_)
        | Self::Case { .. } => matches!(ret, Sort::Computation),
        | Self::PathUniverse(..)
        | Self::Base(_)
        | Self::UnitType
        | Self::Product(..)
        | Self::Sum(..)
        | Self::ThunkType(_)
        | Self::Universe { .. }
        | Self::TypeLift { .. }
        | Self::Element { .. }
        | Self::Abstract(_)
        | Self::StaticPi { .. } => matches!(ret, Sort::ValueType),
        | Self::Returner(_)
        | Self::Arrow { .. }
        | Self::Pi { .. }
        | Self::ComputationElement { .. } => matches!(ret, Sort::CompType),
        | Self::Unresolved(sort) => matches!(
            (sort, ret),
            (Sort::Value, Sort::Value)
                | (Sort::Computation, Sort::Computation)
                | (Sort::ValueType, Sort::ValueType)
                | (Sort::CompType, Sort::CompType)
        ),
    })]
    pub(crate) const fn sort(&self) -> Sort
    {
        match *self {
            | Self::PathRefl(_)
            | Self::PrimitiveValue(_)
            | Self::PathProduct(..)
            | Self::PathEquiv { .. }
            | Self::Variable { .. }
            | Self::Constant(_)
            | Self::Unit
            | Self::Literal(_)
            | Self::Pair(..)
            | Self::Injection(..)
            | Self::Thunk(_)
            | Self::ValueLift { .. }
            | Self::Quote(_)
            | Self::QuoteComputation(_)
            | Self::StaticLambda(_)
            | Self::StaticApplication(..) => Sort::Value,
            | Self::Transport(..)
            | Self::Primitive(..)
            | Self::Lambda(_)
            | Self::Application(..)
            | Self::Return(_)
            | Self::Bind(..)
            | Self::Force(_)
            | Self::Case { .. } => Sort::Computation,
            | Self::PathUniverse(..)
            | Self::Base(_)
            | Self::UnitType
            | Self::Product(..)
            | Self::Sum(..)
            | Self::ThunkType(_)
            | Self::Universe { .. }
            | Self::TypeLift { .. }
            | Self::Element { .. }
            | Self::Abstract(_)
            | Self::StaticPi { .. } => Sort::ValueType,
            | Self::Returner(_)
            | Self::Arrow { .. }
            | Self::Pi { .. }
            | Self::ComputationElement { .. } => Sort::CompType,
            | Self::Unresolved(sort) => sort,
        }
    }

    /// The node's children, in order, each with the sort its former requires.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every child index the node holds, left to right, beside the
    ///   sort the core vocabulary gives that position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared edges and interleaved signature roots test
    ///   graph discovery; the finite persistence corpus supplies selected edges
    ///   across the four sorts. This is not exhaustive evidence for all graphs.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| {
        use Sort::CompType as C;
        use Sort::Computation as M;
        use Sort::Value as V;
        use Sort::ValueType as A;
        let actual = ret.slots.get(.. ret.count);
        match *self {
            | Self::Primitive(_, arguments) => actual.is_some_and(|children| children.iter().copied().eq(arguments.iter().copied().map(|argument| (argument, V)))),
            | Self::PrimitiveValue(_) | Self::Variable { .. }
            | Self::Constant(_)
            | Self::Unit
            | Self::Literal(_)
            | Self::Base(_)
            | Self::UnitType
            | Self::Universe { .. }
            | Self::Abstract(_)
            | Self::Unresolved(_) => ret.count == 0,
            | Self::Pair(a, b) | Self::StaticApplication(a, b) | Self::PathUniverse(a, b) | Self::PathProduct(a, b) | Self::Transport(a, b) => {
                actual == Some(&[(a, V), (b, V)][..])
            },
            | Self::PathEquiv { path_type, forward, backward, .. } => actual == Some(&[(path_type, A), (forward, V), (backward, V)][..]),
            | Self::PathRefl(a)
            | Self::StaticLambda(a)
            | Self::Injection(_, a)
            | Self::ValueLift { body: a, .. }
            | Self::Return(a)
            | Self::Force(a)
            | Self::Element { code: a, .. }
            | Self::ComputationElement { code: a, .. } => actual == Some(&[(a, V)][..]),
            | Self::Thunk(a) | Self::Lambda(a) => actual == Some(&[(a, M)][..]),
            | Self::Application(a, b) => actual == Some(&[(a, M), (b, V)][..]),
            | Self::Bind(a, b) => actual == Some(&[(a, M), (b, M)][..]),
            | Self::Case {
                scrutinee: a,
                on_left: b,
                on_right: c,
            } => actual == Some(&[(a, V), (b, M), (c, M)][..]),
            | Self::Product(a, b)
            | Self::Sum(a, b)
            | Self::StaticPi {
                domain: a,
                codomain: b,
            } => actual == Some(&[(a, A), (b, A)][..]),
            | Self::ThunkType(a) | Self::QuoteComputation(a) => actual == Some(&[(a, C)][..]),
            | Self::TypeLift { inner: a, .. } | Self::Returner(a) | Self::Quote(a) => {
                actual == Some(&[(a, A)][..])
            },
            | Self::Arrow {
                domain: a,
                codomain: b,
            }
            | Self::Pi {
                domain: a,
                codomain: b,
            } => actual == Some(&[(a, A), (b, C)][..]),
        }
    })]
    pub(crate) fn children(&self) -> Children
    {
        use Sort::CompType as C;
        use Sort::Computation as M;
        use Sort::Value as V;
        use Sort::ValueType as A;
        match *self {
            | Self::Primitive(_, arguments) => match arguments {
                | gandr_core_term::primitive::Arguments::Unary(argument) => {
                    Children::of(&[(argument, V)])
                },
                | gandr_core_term::primitive::Arguments::Binary([first, second]) => {
                    Children::of(&[(first, V), (second, V)])
                },
            },
            | Self::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => Children::of(&[(path_type, A), (forward, V), (backward, V)]),
            | Self::PrimitiveValue(_)
            | Self::Variable { .. }
            | Self::Constant(_)
            | Self::Unit
            | Self::Literal(_)
            | Self::Base(_)
            | Self::UnitType
            | Self::Universe { .. }
            | Self::Abstract(_)
            | Self::Unresolved(_) => Children::default(),
            | Self::PathUniverse(first, second)
            | Self::PathProduct(first, second)
            | Self::Transport(first, second)
            | Self::Pair(first, second)
            | Self::StaticApplication(first, second) => Children::of(&[(first, V), (second, V)]),
            | Self::PathRefl(body)
            | Self::StaticLambda(body)
            | Self::Injection(_, body)
            | Self::ValueLift { body, .. }
            | Self::Return(body)
            | Self::Force(body) => Children::of(&[(body, V)]),
            | Self::Thunk(body) | Self::Lambda(body) => Children::of(&[(body, M)]),
            | Self::Application(head, argument) => Children::of(&[(head, M), (argument, V)]),
            | Self::Bind(bound, rest) => Children::of(&[(bound, M), (rest, M)]),
            | Self::Case {
                scrutinee,
                on_left,
                on_right,
            } => Children::of(&[(scrutinee, V), (on_left, M), (on_right, M)]),
            | Self::Product(first, second)
            | Self::Sum(first, second)
            | Self::StaticPi {
                domain: first,
                codomain: second,
            } => Children::of(&[(first, A), (second, A)]),
            | Self::ThunkType(body) => Children::of(&[(body, C)]),
            | Self::TypeLift { inner, .. } | Self::Returner(inner) => Children::of(&[(inner, A)]),
            | Self::Element { code, .. } | Self::ComputationElement { code, .. } => {
                Children::of(&[(code, V)])
            },
            | Self::Quote(quoted) => Children::of(&[(quoted, A)]),
            | Self::QuoteComputation(quoted) => Children::of(&[(quoted, C)]),
            | Self::Arrow { domain, codomain } | Self::Pi { domain, codomain } => {
                Children::of(&[(domain, A), (codomain, C)])
            },
        }
    }

    /// The reference a constant or an abstract type names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the borrowed reference for Constant or Abstract, otherwise
    ///   `NotAReference`; the predicate checks the presence classification.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the footprint corpus separates reachable references
    ///   from unreachable and unresolved entries; the attribute does not assert
    ///   borrowed payload identity in a const expression.
    /// - witness: `footprint::tests::bounded_tables_separate_reachability_opacity_and_holes`
    #[spec(ensures: |ret| match *self {
        Self::Constant(_) | Self::Abstract(_) => matches!(ret, Maybe::Present(_)),
        _ => matches!(ret, Maybe::Absent(referencing::Absent::NotAReference)),
    })]
    pub(crate) const fn reference(&self) -> Maybe<&Reference, referencing::Absent>
    {
        match *self {
            | Self::Constant(ref reference) | Self::Abstract(ref reference) => {
                Maybe::Present(reference)
            },
            | Self::PathUniverse(..)
            | Self::PrimitiveValue(_)
            | Self::Primitive(..)
            | Self::PathRefl(_)
            | Self::PathProduct(..)
            | Self::PathEquiv { .. }
            | Self::Transport(..)
            | Self::Variable { .. }
            | Self::Unit
            | Self::Literal(_)
            | Self::Pair(..)
            | Self::Injection(..)
            | Self::Thunk(_)
            | Self::ValueLift { .. }
            | Self::Lambda(_)
            | Self::Application(..)
            | Self::Return(_)
            | Self::Bind(..)
            | Self::Force(_)
            | Self::Case { .. }
            | Self::Base(_)
            | Self::UnitType
            | Self::Product(..)
            | Self::Sum(..)
            | Self::ThunkType(_)
            | Self::Universe { .. }
            | Self::TypeLift { .. }
            | Self::Element { .. }
            | Self::Returner(_)
            | Self::Arrow { .. }
            | Self::Pi { .. }
            | Self::Quote(_)
            | Self::QuoteComputation(_)
            | Self::StaticLambda(_)
            | Self::StaticApplication(..)
            | Self::StaticPi { .. }
            | Self::ComputationElement { .. }
            | Self::Unresolved(_) => Maybe::Absent(referencing::Absent::NotAReference),
        }
    }
}

/// Where an arena node sits in the table of the item that reached it.
///
/// # Specification
/// - executable: none — the map alone cannot establish which arena and walk
///   produced its entries.
///
/// # Adequacy
/// - hypothesis: L2 — the projection witness separates all four node families
///   and an unreached identifier in the same arena.
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Sites(BTreeMap<ArenaNode, NodeIndex>);

impl Sites
{
    /// The table index of `node`, when the item's walk reached it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the recorded index exactly, or Unreached if absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — projection checks all four node families and an
    ///   unreached identifier in the same arena.
    /// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
    #[spec(ensures: |ret| match self.0.get(&node) {
        Some(&index) => ret == Maybe::Present(index),
        None => ret == Maybe::Absent(site::Absent::Unreached),
    })]
    pub(crate) fn of(
        &self,
        node: ArenaNode,
    ) -> Maybe<NodeIndex, site::Absent>
    {
        match self.0.get(&node) {
            | Some(&index) => Maybe::Present(index),
            | None => Maybe::Absent(site::Absent::Unreached),
        }
    }
}

/// Whether a table holds an id another arena minted.
///
/// # Specification
/// - executable: none — the tag contains no table; `opacity_of` establishes its
///   correspondence.
///
/// # Adequacy
/// - hypothesis: L2 — a foreign unresolved value makes content opaque; the
///   supported persistence corpus supplies resolving tables.
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Opacity
{
    /// Every node resolved.
    Transparent,
    /// Some node did not resolve; the item is never adopted or persisted.
    Opaque,
}

/// An item's canonical content: its reference and its two halves as one table.
///
/// # Specification
/// - executable: none — stored roots and entries do not retain an arena; raw
///   reconstruction is not validation.
///
/// # Adequacy
/// - hypothesis: L3 — noisy arenas, sharing, unresolved identifiers and
///   signature extraction bound the encoding evidence; arbitrary raw tables are
///   not certified by this representation.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ItemContent
{
    /// The item's own reference: its key and occurrence.
    reference: Reference,
    /// The signature's root, or why there is none.
    signature: Maybe<NodeIndex, signature::Absent>,
    /// The body's root, or why there is none.
    body: Maybe<NodeIndex, body::Absent>,
    /// Every node reachable from the roots, numbered by discovery.
    nodes: Vec<ContentNode>,
}

impl ItemContent
{
    /// The item's own reference.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reference(&self) -> &Reference
    {
        &self.reference
    }

    /// The signature's root, or why there is none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn signature(&self) -> Maybe<NodeIndex, signature::Absent>
    {
        self.signature
    }

    /// The body's root, or why there is none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn body(&self) -> Maybe<NodeIndex, body::Absent>
    {
        self.body
    }

    /// Every node reachable from the roots, numbered by discovery.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ContentNode]
    {
        &self.nodes
    }

    /// The content of these parts, as the decoder reassembles it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_parts(
        reference: Reference,
        signature: Maybe<NodeIndex, signature::Absent>,
        body: Maybe<NodeIndex, body::Absent>,
        nodes: Vec<ContentNode>,
    ) -> Self
    {
        Self {
            reference,
            signature,
            body,
            nodes,
        }
    }

    /// Whether every node of the item resolved.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn opacity(&self) -> Opacity
    {
        opacity_of(&self.nodes)
    }

    /// The signature's type, as a type table of its own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the table of every node reachable from the signature root,
    ///   renumbered by discovery from that root alone, so it equals the table
    ///   [`TypeContent::of_value_type`] gives the signature in its arena.
    /// - provides: `signature::Absent::Unsigned` for an unsigned item.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an interleaved signature is compared with
    ///   independently encoding its root. Raw malformed roots are not covered
    ///   by that witness.
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref content) => match self.signature {
            Maybe::Present(root) => self.nodes.get(usize::from(root)).map_or_else(
                || content.nodes == [ContentNode::Unresolved(Sort::Value)],
                |node| content.nodes.first().is_some_and(|first| first.sort() == node.sort()),
            ),
            Maybe::Absent(_) => false,
        },
        Maybe::Absent(reason) => self.signature == Maybe::Absent(reason),
    })]
    pub(crate) fn signature_type(&self) -> Maybe<TypeContent, signature::Absent>
    {
        match self.signature {
            | Maybe::Present(root) => Maybe::Present(TypeContent {
                nodes: renumber(&self.nodes, root),
            }),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// A type's canonical content: every node reachable from it, numbered by
/// discovery, the type itself first.
///
/// # Specification
/// - executable: none — the raw table constructor admits malformed graphs;
///   canonicality is a producer or decoder obligation.
///
/// # Adequacy
/// - hypothesis: L3 — independent type encoding and minting preserve a shared
///   arrow; a finite malformed corpus separates the five named mint refusals.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypeContent
{
    /// The nodes; the root is the first.
    nodes: Vec<ContentNode>,
}

impl TypeContent
{
    /// The nodes; the root is the first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ContentNode]
    {
        &self.nodes
    }

    /// The content of these nodes, as the decoder reassembles it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_nodes(nodes: Vec<ContentNode>) -> Self
    {
        Self { nodes }
    }

    /// The content of the value type `ty` of `program`'s arena.
    ///
    /// # Specification
    /// - requires: nothing — an unresolved id is admissible and listed as
    ///   unresolved.
    /// - ensures: the table the item encoding gives the same node, renumbered
    ///   from it, so a type compares equal to itself across arenas.
    /// - provides: the comparison form of types: answers, verdicts and seats
    ///   are compared by it, never by arena id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — allocation noise and a shared arrow separate arena
    ///   identity from content; the same signature is encoded through the item
    ///   path.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| match program.arena().value_type(ty) {
            | Some(_) => ret.nodes.first().is_some_and(|node| {
                node.sort() == Sort::ValueType && !matches!(*node, ContentNode::Unresolved(_))
            }),
            | None => ret.nodes == [ContentNode::Unresolved(Sort::ValueType)],
        })]
    #[inline]
    #[must_use]
    pub fn of_value_type(
        program: &Program,
        ty: ValueTypeId,
    ) -> Self
    {
        Self::of(program.arena(), program.layout(), ArenaNode::ValueType(ty))
    }

    /// The content of the node `root` of `arena`, constants resolved through
    /// `layout`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the discovery-numbered table of every node reachable from
    ///   `root`, `root` first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent type extraction and shared-node minting
    ///   exercise a rooted value-type graph; other root families are not
    ///   claimed here.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| {
            ret.nodes.first().is_some_and(|node| {
                node.sort()
                    == match root {
                        | ArenaNode::Value(_) => Sort::Value,
                        | ArenaNode::Computation(_) => Sort::Computation,
                        | ArenaNode::ValueType(_) => Sort::ValueType,
                        | ArenaNode::CompType(_) => Sort::CompType,
                    }
            }) && ret.nodes.iter().all(|node| {
                node.children()
                    .iter()
                    .all(|(child, _)| usize::from(child) < ret.nodes.len())
            })
        })]
    pub(crate) fn of(
        arena: &CoreArena,
        layout: &Layout,
        root: ArenaNode,
    ) -> Self
    {
        let mut encoder = Encoder::new(arena, layout);
        let _root = encoder.discover(root);
        encoder.drain();
        Self {
            nodes: encoder.nodes,
        }
    }

    /// Every reference the type names, anywhere in it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: all stored Constant and Abstract references in table order,
    ///   including duplicates.
    /// - executable: none — anodized 0.7 emits an invalid closure return type
    ///   for this opaque iterator, including for preconditions alone.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — with no footprint type reads, changing either an
    ///   abstract reference or a code reference inside a recorded answer
    ///   invalidates it; an unrelated change and an untyped answer do not.
    ///   These are constructed guard inputs, not a claim of checker provenance.
    /// - witness: `checkpoint::tests::recorded_answer_references_participate_in_value_invalidation`
    pub(crate) fn references(&self) -> impl Iterator<Item = &Reference>
    {
        self.nodes.iter().filter_map(|node| match node.reference() {
            | Maybe::Present(reference) => Some(reference),
            | Maybe::Absent(_) => None,
        })
    }

    /// Mint the type into `arena`, constants placed through `layout`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success a value type of `arena` whose content is this
    ///   table, its shared nodes minted once.
    /// - provides: the seat an adopted synthesised type is read from.
    /// - fails: `seating::Absent` naming why: an unresolved node, a cycle, a
    ///   reference the program does not hold, a table that is no value type, or
    ///   a former holding a term, which a seat never needs while formed types
    ///   hold none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shared arrow is minted back into a noisy arena; one
    ///   table for each of the five refusal reasons bounds error evidence. The
    ///   predicate checks successful seat resolution, not a second encoding.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(id) => arena.value_type(id).is_some(),
        Maybe::Absent(_) => true,
    })]
    pub(crate) fn mint(
        &self,
        arena: &mut CoreArena,
        layout: &Layout,
    ) -> Maybe<ValueTypeId, seating::Absent>
    {
        match mint_table(&self.nodes, arena, layout) {
            | Maybe::Present(Minted::ValueType(id)) => Maybe::Present(id),
            | Maybe::Present(Minted::CompType(_)) => Maybe::Absent(seating::Absent::IllSorted),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }
}

/// An item's content beside where its arena nodes sit in it.
///
/// # Specification
/// - executable: none — the pair does not retain its source arena;
///   correspondence is established by `encode_item`.
///
/// # Adequacy
/// - hypothesis: L2 — item identity and the site projection are checked through
///   their actual consumers, not inferred from the pair alone.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `typing::tests::refusal_payloads_use_item_coordinates_and_type_content`
pub struct Encoded
{
    /// The content.
    pub content: ItemContent,
    /// The table index of every arena node the walk reached.
    pub sites: Sites,
}

/// The content of the item at `ordinal` of a program.
///
/// # Specification
/// - requires: nothing; an ordinal outside `layout` encodes an empty unsigned
///   hole under an unoccupied reference.
/// - ensures: the item's reference, its two roots and the discovery-numbered
///   table of every node reachable from them, the signature's root first.
/// - provides: the item's identity, the sites its verdict is projected through,
///   and the table its footprint is read from — one walk for all three.
/// - panics: none.
/// - intension: reads each reachable node once and allocates one table entry
///   per distinct node.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the discovery order, the sharing and the
///   id-freedom, separated by two arenas building one item in different
///   allocation orders, a shared subterm listed once, a constant resolved to
///   its item's reference, and an unresolved id listed by sort.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[spec(ensures: |ret| ret.sites.0.len() == ret.content.nodes.len()
    && ret.sites.0.values().all(|index| usize::from(*index) < ret.content.nodes.len())
    && match layout.items.get(usize::from(ordinal)) {
        Some(item) => layout.references.get(usize::from(ordinal)) == Some(&ret.content.reference)
            && match (item.declaration().signature(), ret.content.signature) {
                (Maybe::Present(_), Maybe::Present(root)) => usize::from(root) == 0,
                (Maybe::Absent(reason), Maybe::Absent(returned)) => reason == returned,
                _ => false,
            }
            && matches!((item.declaration().body(), ret.content.body),
                (Maybe::Present(_), Maybe::Present(_)) | (Maybe::Absent(_), Maybe::Absent(_))),
        None => ret.content.reference == Reference::Unoccupied
            && ret.content.signature == Maybe::Absent(signature::Absent::Unsigned)
            && ret.content.body == Maybe::Absent(body::Absent::Hole)
            && ret.content.nodes.is_empty(),
    })]
pub fn encode_item(
    arena: &CoreArena,
    layout: &Layout,
    ordinal: crate::boundary::ItemOrdinal,
) -> Encoded
{
    let mut encoder = Encoder::new(arena, layout);
    let (reference, signature, body) = match layout.items.get(usize::from(ordinal)) {
        | Some(item) => {
            let declaration = item.declaration();
            let signature = declaration
                .signature()
                .map(|ty| encoder.discover(ArenaNode::ValueType(ty)));
            let body = declaration
                .body()
                .map(|term| encoder.discover(ArenaNode::Value(term)));
            let reference = layout
                .references
                .get(usize::from(ordinal))
                .cloned()
                .unwrap_or(Reference::Unoccupied);
            (reference, signature, body)
        },
        | None => (
            Reference::Unoccupied,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
        ),
    };
    encoder.drain();
    Encoded {
        content: ItemContent {
            reference,
            signature,
            body,
            nodes: encoder.nodes,
        },
        sites: Sites(encoder.seen),
    }
}

/// Whether `nodes` holds an unresolved node.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Opaque exactly when any entry is Unresolved.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — unresolved foreign content and the supported persistence
///   corpus separate opaque and resolving tables.
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(ensures: |ret| (ret == Opacity::Opaque)
    == nodes.iter().any(|node| matches!(*node, ContentNode::Unresolved(_))))]
pub fn opacity_of(nodes: &[ContentNode]) -> Opacity
{
    if nodes
        .iter()
        .any(|node| matches!(*node, ContentNode::Unresolved(_)))
    {
        Opacity::Opaque
    }
    else {
        Opacity::Transparent
    }
}

/// The breadth-first walk that numbers an arena graph by discovery.
///
/// # Specification
/// - executable: none — queue order and first discovery relate mutable fields
///   over a walk, not a callable type declaration.
///
/// # Adequacy
/// - hypothesis: L3 — distinct arena allocations, shared nodes and interleaved
///   roots separate the breadth-first identity cases without a universal graph
///   claim.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
struct Encoder<'arena, 'layout>
{
    /// The arena read.
    arena: &'arena CoreArena,
    /// The program positions resolve through.
    layout: &'layout Layout,
    /// The number each discovered node took.
    seen: BTreeMap<ArenaNode, NodeIndex>,
    /// The discovered nodes not yet written, in discovery order.
    queue: VecDeque<ArenaNode>,
    /// The written nodes, in discovery order.
    nodes: Vec<ContentNode>,
}

impl<'arena, 'layout> Encoder<'arena, 'layout>
{
    /// An empty walk over `arena`.
    ///
    /// # Specification
    /// trivial.
    const fn new(
        arena: &'arena CoreArena,
        layout: &'layout Layout,
    ) -> Self
    {
        Self {
            arena,
            layout,
            seen: BTreeMap::new(),
            queue: VecDeque::new(),
            nodes: Vec::new(),
        }
    }

    /// The number of `node`, numbering and queueing it on first discovery.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number `node` took when first discovered; a node
    ///   discovered now takes the next number and joins the queue.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a shared node retains one number; separately
    ///   allocated equal nodes retain distinct numbers.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    #[spec(
        captures: [old = self.seen.get(&node).copied(), count = self.seen.len(), queued = self.queue.len()],
        ensures: |ret| self.seen.get(&node) == Some(&ret) && match old {
            Some(index) => ret == index && self.seen.len() == count && self.queue.len() == queued,
            None => usize::from(ret) == count && self.seen.len() == count.saturating_add(1)
                && self.queue.len() == queued.saturating_add(1) && self.queue.back() == Some(&node),
        },
    )]
    fn discover(
        &mut self,
        node: ArenaNode,
    ) -> NodeIndex
    {
        let next = NodeIndex::from(self.seen.len());
        let index = *self.seen.entry(node).or_insert(next);
        if index == next {
            self.queue.push_back(node);
        }
        index
    }

    /// Write every queued node, discovering its children as it is written.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the queue is empty and the table holds one entry per number
    ///   handed out, in number order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — shared and interleaved roots are exhausted into one
    ///   discovery-numbered table.
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: self.queue.is_empty() && self.nodes.len() == self.seen.len()
        && self.seen.values().all(|index| usize::from(*index) < self.nodes.len()))]
    fn drain(&mut self)
    {
        while let Some(node) = self.queue.pop_front() {
            let written = self.read(node);
            self.nodes.push(written);
        }
    }

    /// The content node of `node`, its children discovered left to right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the former of `node` over its children's numbers, a constant
    ///   resolved to its reference, or the unresolved node of its sort.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite corpus exercises four resolving node
    ///   families; the foreign-id witness exercises the unresolved value
    ///   branch.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| ret.sort() == match node {
        ArenaNode::Value(_) => Sort::Value,
        ArenaNode::Computation(_) => Sort::Computation,
        ArenaNode::ValueType(_) => Sort::ValueType,
        ArenaNode::CompType(_) => Sort::CompType,
    })]
    fn read(
        &mut self,
        node: ArenaNode,
    ) -> ContentNode
    {
        let arena = self.arena;
        match node {
            | ArenaNode::Value(id) => match arena.value(id) {
                | Some(value) => self.read_value(value),
                | None => ContentNode::Unresolved(Sort::Value),
            },
            | ArenaNode::Computation(id) => match arena.computation(id) {
                | Some(computation) => self.read_computation(computation),
                | None => ContentNode::Unresolved(Sort::Computation),
            },
            | ArenaNode::ValueType(id) => match arena.value_type(id) {
                | Some(value_type) => self.read_value_type(value_type),
                | None => ContentNode::Unresolved(Sort::ValueType),
            },
            | ArenaNode::CompType(id) => match arena.comp_type(id) {
                | Some(comp_type) => self.read_comp_type(comp_type),
                | None => ContentNode::Unresolved(Sort::CompType),
            },
        }
    }

    /// The content node of a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::Value
        && !matches!(ret, ContentNode::Unresolved(_))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_value(
        &mut self,
        value: &Value,
    ) -> ContentNode
    {
        match *value {
            | Value::Primitive { primitive, .. } => ContentNode::PrimitiveValue(primitive),
            | Value::PathRefl(code) => ContentNode::PathRefl(self.discover(ArenaNode::Value(code))),
            | Value::PathProduct(first, second) => {
                let first = self.discover(ArenaNode::Value(first));
                ContentNode::PathProduct(first, self.discover(ArenaNode::Value(second)))
            },
            | Value::PathEquiv {
                path_type,
                forward,
                backward,
                ref evidence,
            } => ContentNode::PathEquiv {
                path_type: self.discover(ArenaNode::ValueType(path_type)),
                forward: self.discover(ArenaNode::Value(forward)),
                backward: self.discover(ArenaNode::Value(backward)),
                evidence: alloc::sync::Arc::clone(evidence),
            },
            | Value::Variable { zone, index } => ContentNode::Variable { zone, index },
            | Value::Constant(position) => ContentNode::Constant(self.layout.resolve(position)),
            | Value::Unit => ContentNode::Unit,
            | Value::Literal(ref literal) => ContentNode::Literal(literal.clone()),
            | Value::Pair(first, second) => {
                let first = self.discover(ArenaNode::Value(first));
                ContentNode::Pair(first, self.discover(ArenaNode::Value(second)))
            },
            | Value::Injection(side, body) => {
                ContentNode::Injection(side, self.discover(ArenaNode::Value(body)))
            },
            | Value::Thunk(body) => ContentNode::Thunk(self.discover(ArenaNode::Computation(body))),
            | Value::Lift { ref target, body } => ContentNode::ValueLift {
                target: target.clone(),
                body: self.discover(ArenaNode::Value(body)),
            },
            | Value::Quote(quoted) => {
                ContentNode::Quote(self.discover(ArenaNode::ValueType(quoted)))
            },
            | Value::QuoteComputation(quoted) => {
                ContentNode::QuoteComputation(self.discover(ArenaNode::CompType(quoted)))
            },
            | Value::StaticLambda(body) => {
                ContentNode::StaticLambda(self.discover(ArenaNode::Value(body)))
            },
            | Value::StaticApplication(head, argument) => {
                let head = self.discover(ArenaNode::Value(head));
                ContentNode::StaticApplication(head, self.discover(ArenaNode::Value(argument)))
            },
        }
    }

    /// The content node of a computation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::Computation
        && !matches!(ret, ContentNode::Unresolved(_))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_computation(
        &mut self,
        computation: &Computation,
    ) -> ContentNode
    {
        match *computation {
            | Computation::Primitive {
                primitive,
                arguments,
            } => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    | Arguments::Unary(argument) => {
                        Arguments::Unary(self.discover(ArenaNode::Value(argument)))
                    },
                    | Arguments::Binary([first, second]) => {
                        let first = self.discover(ArenaNode::Value(first));
                        Arguments::Binary([first, self.discover(ArenaNode::Value(second))])
                    },
                };
                ContentNode::Primitive(primitive, arguments)
            },
            | Computation::Transport(path, value) => {
                let path = self.discover(ArenaNode::Value(path));
                ContentNode::Transport(path, self.discover(ArenaNode::Value(value)))
            },
            | Computation::Lambda(body) => {
                ContentNode::Lambda(self.discover(ArenaNode::Computation(body)))
            },
            | Computation::Application(head, argument) => {
                let head = self.discover(ArenaNode::Computation(head));
                ContentNode::Application(head, self.discover(ArenaNode::Value(argument)))
            },
            | Computation::Return(value) => {
                ContentNode::Return(self.discover(ArenaNode::Value(value)))
            },
            | Computation::Bind(bound, rest) => {
                let bound = self.discover(ArenaNode::Computation(bound));
                ContentNode::Bind(bound, self.discover(ArenaNode::Computation(rest)))
            },
            | Computation::Force(value) => {
                ContentNode::Force(self.discover(ArenaNode::Value(value)))
            },
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => {
                let scrutinee = self.discover(ArenaNode::Value(scrutinee));
                let on_left = self.discover(ArenaNode::Computation(on_left));
                ContentNode::Case {
                    scrutinee,
                    on_left,
                    on_right: self.discover(ArenaNode::Computation(on_right)),
                }
            },
        }
    }

    /// The content node of a value type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::ValueType
        && !matches!(ret, ContentNode::Unresolved(_))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_value_type(
        &mut self,
        value_type: &ValueType,
    ) -> ContentNode
    {
        match *value_type {
            | ValueType::PathUniverse(source, target) => {
                let source = self.discover(ArenaNode::Value(source));
                ContentNode::PathUniverse(source, self.discover(ArenaNode::Value(target)))
            },
            | ValueType::Base(base) => ContentNode::Base(base),
            | ValueType::Unit => ContentNode::UnitType,
            | ValueType::Product(first, second) => {
                let first = self.discover(ArenaNode::ValueType(first));
                ContentNode::Product(first, self.discover(ArenaNode::ValueType(second)))
            },
            | ValueType::Sum(first, second) => {
                let first = self.discover(ArenaNode::ValueType(first));
                ContentNode::Sum(first, self.discover(ArenaNode::ValueType(second)))
            },
            | ValueType::Thunk(body) => {
                ContentNode::ThunkType(self.discover(ArenaNode::CompType(body)))
            },
            | ValueType::Universe { sort, ref level } => ContentNode::Universe {
                sort,
                level: level.clone(),
            },
            | ValueType::Lift { inner, ref target } => ContentNode::TypeLift {
                inner: self.discover(ArenaNode::ValueType(inner)),
                target: target.clone(),
            },
            | ValueType::Element { code, ref target } => ContentNode::Element {
                code: self.discover(ArenaNode::Value(code)),
                target: target.clone(),
            },
            | ValueType::Abstract(position) => ContentNode::Abstract(self.layout.resolve(position)),
            | ValueType::StaticPi { domain, codomain } => {
                let domain = self.discover(ArenaNode::ValueType(domain));
                ContentNode::StaticPi {
                    domain,
                    codomain: self.discover(ArenaNode::ValueType(codomain)),
                }
            },
        }
    }

    /// The content node of a computation type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the corresponding former with child ids replaced by their
    ///   discovery indices; the predicate bounds the sort and child indices.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite persistence corpus exercises selected
    ///   formers and sharing. The attribute does not independently reconstruct
    ///   every payload.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    #[spec(ensures: |ret| ret.sort() == Sort::CompType
        && !matches!(ret, ContentNode::Unresolved(_))
        && ret.children().iter().all(|(child, _)| usize::from(child) < self.seen.len()))]
    fn read_comp_type(
        &mut self,
        comp_type: &CompType,
    ) -> ContentNode
    {
        match *comp_type {
            | CompType::Returner(result) => {
                ContentNode::Returner(self.discover(ArenaNode::ValueType(result)))
            },
            | CompType::Arrow { domain, codomain } => {
                let domain = self.discover(ArenaNode::ValueType(domain));
                ContentNode::Arrow {
                    domain,
                    codomain: self.discover(ArenaNode::CompType(codomain)),
                }
            },
            | CompType::Pi { domain, codomain } => {
                let domain = self.discover(ArenaNode::ValueType(domain));
                ContentNode::Pi {
                    domain,
                    codomain: self.discover(ArenaNode::CompType(codomain)),
                }
            },
            | CompType::Element { code, ref target } => ContentNode::ComputationElement {
                code: self.discover(ArenaNode::Value(code)),
                target: target.clone(),
            },
        }
    }
}

/// The table of every node reachable from `root` in `nodes`, renumbered by
/// discovery from `root`.
///
/// # Specification
/// - requires: nothing — an out-of-range child is listed as unresolved.
/// - ensures: the table a walk from `root` alone would have written.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an interleaved signature is compared with independent
///   encoding; cyclic, dangling, leaf and absent roots are checked against
///   explicit discovery-numbered tables.
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `content::tests::renumbering_closes_dangling_and_cyclic_tables`
#[spec(ensures: |ret| {
        nodes.get(usize::from(root)).map_or_else(
            || ret == [ContentNode::Unresolved(Sort::Value)],
            |node| ret.first().is_some_and(|first| first.sort() == node.sort()),
        ) && ret.iter().all(|node| {
            node.children()
                .iter()
                .all(|(child, _)| usize::from(child) < ret.len())
        })
    })]
pub fn renumber(
    nodes: &[ContentNode],
    root: NodeIndex,
) -> Vec<ContentNode>
{
    let mut numbers: BTreeMap<NodeIndex, NodeIndex> = BTreeMap::new();
    let mut queue = VecDeque::new();
    let mut table = Vec::new();
    let _root = numbers.insert(root, NodeIndex::from(0_usize));
    queue.push_back(root);
    while let Some(old) = queue.pop_front() {
        let Some(node) = nodes.get(usize::from(old))
        else {
            table.push(ContentNode::Unresolved(Sort::Value));
            continue;
        };
        let mut discover = |child: NodeIndex| {
            let next = NodeIndex::from(numbers.len());
            let number = *numbers.entry(child).or_insert(next);
            if number == next {
                queue.push_back(child);
            }
            number
        };
        table.push(map_children(node, &mut discover));
    }
    table
}

/// `node` with every child index replaced by its image under `image`, applied
/// left to right.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the former and non-child payloads are retained; each child is
///   replaced by one call to `image`, in left-to-right order. The predicate
///   checks the former, sort and child-slot sorts without recalling `image`.
/// - panics: propagates a panic from `image`.
///
/// # Adequacy
/// - hypothesis: L2 — an interleaved signature is renumbered independently. The
///   malformed-table witness checks cycles, dangling children and root
///   selection.
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
/// - witness: `content::tests::renumbering_closes_dangling_and_cyclic_tables`
#[spec(ensures: |ret| {
        core::mem::discriminant(&ret) == core::mem::discriminant(node)
            && ret.sort() == node.sort()
            && ret
                .children()
                .iter()
                .map(|(_, sort)| sort)
                .eq(node.children().iter().map(|(_, sort)| sort))
    })]
#[inline]
pub fn map_children<Image>(
    node: &ContentNode,
    image: &mut Image,
) -> ContentNode
where
    Image: FnMut(NodeIndex) -> NodeIndex,
{
    match *node {
        | ContentNode::PrimitiveValue(primitive) => ContentNode::PrimitiveValue(primitive),
        | ContentNode::Primitive(primitive, mut arguments) => {
            for argument in arguments.iter_mut() {
                *argument = image(*argument);
            }
            ContentNode::Primitive(primitive, arguments)
        },
        | ContentNode::PathUniverse(source, target) => {
            let source = image(source);
            ContentNode::PathUniverse(source, image(target))
        },
        | ContentNode::PathRefl(code) => ContentNode::PathRefl(image(code)),
        | ContentNode::PathProduct(first, second) => {
            let first = image(first);
            ContentNode::PathProduct(first, image(second))
        },
        | ContentNode::PathEquiv {
            path_type,
            forward,
            backward,
            ref evidence,
        } => ContentNode::PathEquiv {
            path_type: image(path_type),
            forward: image(forward),
            backward: image(backward),
            evidence: alloc::sync::Arc::clone(evidence),
        },
        | ContentNode::Transport(path, value) => {
            let path = image(path);
            ContentNode::Transport(path, image(value))
        },
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::Unit
        | ContentNode::Literal(_)
        | ContentNode::Base(_)
        | ContentNode::UnitType
        | ContentNode::Universe { .. }
        | ContentNode::Abstract(_)
        | ContentNode::Unresolved(_) => node.clone(),
        | ContentNode::Pair(first, second) => {
            let first = image(first);
            ContentNode::Pair(first, image(second))
        },
        | ContentNode::Injection(side, body) => ContentNode::Injection(side, image(body)),
        | ContentNode::Thunk(body) => ContentNode::Thunk(image(body)),
        | ContentNode::ValueLift { ref target, body } => ContentNode::ValueLift {
            target: target.clone(),
            body: image(body),
        },
        | ContentNode::Lambda(body) => ContentNode::Lambda(image(body)),
        | ContentNode::Application(head, argument) => {
            let head = image(head);
            ContentNode::Application(head, image(argument))
        },
        | ContentNode::Return(value) => ContentNode::Return(image(value)),
        | ContentNode::Bind(bound, rest) => {
            let bound = image(bound);
            ContentNode::Bind(bound, image(rest))
        },
        | ContentNode::Force(value) => ContentNode::Force(image(value)),
        | ContentNode::Case {
            scrutinee,
            on_left,
            on_right,
        } => {
            let scrutinee = image(scrutinee);
            let on_left = image(on_left);
            ContentNode::Case {
                scrutinee,
                on_left,
                on_right: image(on_right),
            }
        },
        | ContentNode::Product(first, second) => {
            let first = image(first);
            ContentNode::Product(first, image(second))
        },
        | ContentNode::Sum(first, second) => {
            let first = image(first);
            ContentNode::Sum(first, image(second))
        },
        | ContentNode::ThunkType(body) => ContentNode::ThunkType(image(body)),
        | ContentNode::TypeLift { inner, ref target } => ContentNode::TypeLift {
            inner: image(inner),
            target: target.clone(),
        },
        | ContentNode::Element { code, ref target } => ContentNode::Element {
            code: image(code),
            target: target.clone(),
        },
        | ContentNode::Returner(result) => ContentNode::Returner(image(result)),
        | ContentNode::Arrow { domain, codomain } => {
            let domain = image(domain);
            ContentNode::Arrow {
                domain,
                codomain: image(codomain),
            }
        },
        | ContentNode::Pi { domain, codomain } => {
            let domain = image(domain);
            ContentNode::Pi {
                domain,
                codomain: image(codomain),
            }
        },
        | ContentNode::Quote(quoted) => ContentNode::Quote(image(quoted)),
        | ContentNode::QuoteComputation(quoted) => ContentNode::QuoteComputation(image(quoted)),
        | ContentNode::StaticLambda(body) => ContentNode::StaticLambda(image(body)),
        | ContentNode::StaticApplication(head, argument) => {
            let head = image(head);
            ContentNode::StaticApplication(head, image(argument))
        },
        | ContentNode::StaticPi { domain, codomain } => {
            let domain = image(domain);
            ContentNode::StaticPi {
                domain,
                codomain: image(codomain),
            }
        },
        | ContentNode::ComputationElement { code, ref target } => ContentNode::ComputationElement {
            code: image(code),
            target: target.clone(),
        },
    }
}

/// A type node minted into an arena.
///
/// # Specification
/// - executable: none — the sort-tagged seat has no arena with which to certify
///   resolution.
///
/// # Adequacy
/// - hypothesis: L2 — A shared arrow is minted into a noisy arena and
///   reconstructed by content.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Minted
{
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// Where the post-order mint stands at one table entry.
///
/// # Specification
/// - executable: none — a traversal marker alone cannot establish the preceding
///   DFS transitions.
///
/// # Adequacy
/// - hypothesis: L2 — Shared-node reuse and a cycle distinguish completed from
///   open entries.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MintState
{
    /// Not reached.
    Fresh,
    /// Reached; its children are being minted.
    Open,
    /// Minted.
    Done(Minted),
}

/// One step of the post-order mint.
///
/// # Specification
/// - executable: none — an individual frame has neither the traversal stack nor
///   its state table.
///
/// # Adequacy
/// - hypothesis: L2 — The shared-arrow and refusal corpus bound post-order
///   traversal evidence.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MintFrame
{
    /// Reach the entry: open it and queue its children.
    Enter(NodeIndex),
    /// Mint the entry from its minted children.
    Exit(NodeIndex),
}

/// Mint the type table `nodes`, rooted at its first entry, into `arena`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the root's minted node; each entry is minted once,
///   after its children.
/// - fails: as [`TypeContent::mint`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a shared arrow is reconstructed after minting; one finite
///   table for each named refusal bounds failures. Empty, dangling and
///   wrong-sort child tables add structural boundaries without claiming
///   arbitrary graphs.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(ensures: |ret| match ret {
    Maybe::Present(Minted::ValueType(id)) => arena.value_type(id).is_some()
        && nodes.first().is_some_and(|node| node.sort() == Sort::ValueType),
    Maybe::Present(Minted::CompType(id)) => arena.comp_type(id).is_some()
        && nodes.first().is_some_and(|node| node.sort() == Sort::CompType),
    Maybe::Absent(reason) => !nodes.is_empty() || reason == seating::Absent::IllSorted,
})]
fn mint_table(
    nodes: &[ContentNode],
    arena: &mut CoreArena,
    layout: &Layout,
) -> Maybe<Minted, seating::Absent>
{
    let mut states = alloc::vec![MintState::Fresh; nodes.len()];
    let mut frames = alloc::vec![MintFrame::Enter(NodeIndex::from(0_usize))];
    while let Some(frame) = frames.pop() {
        match frame {
            | MintFrame::Enter(index) => {
                let (Some(state), Some(node)) = (
                    states.get_mut(usize::from(index)),
                    nodes.get(usize::from(index)),
                )
                else {
                    return Maybe::Absent(seating::Absent::IllSorted);
                };
                match *state {
                    | MintState::Done(_) => {},
                    | MintState::Open => return Maybe::Absent(seating::Absent::Cyclic),
                    | MintState::Fresh => {
                        *state = MintState::Open;
                        frames.push(MintFrame::Exit(index));
                        let children = node.children();
                        let first = frames.len();
                        frames.extend(children.iter().map(|(child, _)| MintFrame::Enter(child)));
                        if let Some(pushed) = frames.get_mut(first ..) {
                            pushed.reverse();
                        }
                    },
                }
            },
            | MintFrame::Exit(index) => {
                let Some(node) = nodes.get(usize::from(index))
                else {
                    return Maybe::Absent(seating::Absent::IllSorted);
                };
                let minted = match mint_node(node, &states, arena, layout) {
                    | Maybe::Present(minted) => minted,
                    | Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
                if let Some(state) = states.get_mut(usize::from(index)) {
                    *state = MintState::Done(minted);
                }
            },
        }
    }
    match states.first() {
        | Some(&MintState::Done(minted)) => Maybe::Present(minted),
        | Some(&(MintState::Fresh | MintState::Open)) | None => {
            Maybe::Absent(seating::Absent::IllSorted)
        },
    }
}

/// The value type minted for the entry `index`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the matching completed seat at `index`, otherwise `IllSorted`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the shared-arrow reconstruction exercises completed
///   seats; malformed child sorts are refused through the enclosing mint. Fresh
///   and open states are not claimed as direct witness coverage.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(ensures: |ret| match states.get(usize::from(index)) {
    Some(&MintState::Done(Minted::ValueType(id))) => ret == Maybe::Present(id),
    _ => ret == Maybe::Absent(seating::Absent::IllSorted),
})]
fn minted_value_type(
    states: &[MintState],
    index: NodeIndex,
) -> Maybe<ValueTypeId, seating::Absent>
{
    match states.get(usize::from(index)) {
        | Some(&MintState::Done(Minted::ValueType(id))) => Maybe::Present(id),
        | Some(&(MintState::Done(Minted::CompType(_)) | MintState::Fresh | MintState::Open))
        | None => Maybe::Absent(seating::Absent::IllSorted),
    }
}

/// The computation type minted for the entry `index`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the matching completed seat at `index`, otherwise `IllSorted`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the shared-arrow reconstruction exercises completed
///   seats; malformed child sorts are refused through the enclosing mint. Fresh
///   and open states are not claimed as direct witness coverage.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(ensures: |ret| match states.get(usize::from(index)) {
    Some(&MintState::Done(Minted::CompType(id))) => ret == Maybe::Present(id),
    _ => ret == Maybe::Absent(seating::Absent::IllSorted),
})]
fn minted_comp_type(
    states: &[MintState],
    index: NodeIndex,
) -> Maybe<CompTypeId, seating::Absent>
{
    match states.get(usize::from(index)) {
        | Some(&MintState::Done(Minted::CompType(id))) => Maybe::Present(id),
        | Some(&(MintState::Done(Minted::ValueType(_)) | MintState::Fresh | MintState::Open))
        | None => Maybe::Absent(seating::Absent::IllSorted),
    }
}

/// Mint one type entry whose children are all minted.
///
/// # Specification
/// - requires: every child of `node` is `Done` in `states`.
/// - ensures: the type node of `node`'s former over its children's minted
///   nodes.
/// - fails: `Unresolved` for an unresolved entry, `Unplaced` for a reference
///   the program does not hold, `IllSorted` for a child of the wrong sort, and
///   `Unseatable` for a former that holds a term.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the shared-arrow graph checks reconstruction; named
///   refusal tables and wrong-sort children bound failures. The predicate
///   checks seat resolution, result sort and refusal class, not a duplicate
///   arena encoding.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
/// - witness: `content::tests::malformed_type_tables_fail_by_structure`
#[spec(
    requires: node.children().iter().all(|(child, _)| matches!(states.get(usize::from(child)), Some(&MintState::Done(_)))),
    ensures: |ret| match ret {
        Maybe::Present(Minted::ValueType(id)) => node.sort() == Sort::ValueType && arena.value_type(id).is_some(),
        Maybe::Present(Minted::CompType(id)) => node.sort() == Sort::CompType && arena.comp_type(id).is_some(),
        Maybe::Absent(reason) => if matches!(*node, ContentNode::Unresolved(_)) {
            reason == seating::Absent::Unresolved
        } else if matches!(node.sort(), Sort::Value | Sort::Computation)
            || matches!(*node, ContentNode::Element { .. } | ContentNode::ComputationElement { .. } | ContentNode::PathUniverse(..)) {
            reason == seating::Absent::Unseatable
        } else {
            reason == seating::Absent::IllSorted || (matches!(*node, ContentNode::Abstract(_)) && reason == seating::Absent::Unplaced)
        },
    },
)]
fn mint_node(
    node: &ContentNode,
    states: &[MintState],
    arena: &mut CoreArena,
    layout: &Layout,
) -> Maybe<Minted, seating::Absent>
{
    let ill_sorted = Maybe::Absent(seating::Absent::IllSorted);
    match *node {
        | ContentNode::Base(base) => Maybe::Present(Minted::ValueType(arena.value_type_base(base))),
        | ContentNode::UnitType => Maybe::Present(Minted::ValueType(arena.value_type_unit())),
        | ContentNode::Universe { sort, ref level } => Maybe::Present(Minted::ValueType(
            arena.value_type_universe(sort, level.clone()),
        )),
        | ContentNode::Abstract(ref reference) => match place(layout, reference) {
            | Maybe::Present(position) => {
                Maybe::Present(Minted::ValueType(arena.value_type_abstract(position)))
            },
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        },
        | ContentNode::Product(first, second) => {
            match (
                minted_value_type(states, first),
                minted_value_type(states, second),
            ) {
                | (Maybe::Present(first), Maybe::Present(second)) => {
                    Maybe::Present(Minted::ValueType(arena.value_type_product(first, second)))
                },
                | _ => ill_sorted,
            }
        },
        | ContentNode::Sum(first, second) => {
            match (
                minted_value_type(states, first),
                minted_value_type(states, second),
            ) {
                | (Maybe::Present(first), Maybe::Present(second)) => {
                    Maybe::Present(Minted::ValueType(arena.value_type_sum(first, second)))
                },
                | _ => ill_sorted,
            }
        },
        | ContentNode::StaticPi { domain, codomain } => {
            match (
                minted_value_type(states, domain),
                minted_value_type(states, codomain),
            ) {
                | (Maybe::Present(domain), Maybe::Present(codomain)) => Maybe::Present(
                    Minted::ValueType(arena.value_type_static_pi(domain, codomain)),
                ),
                | _ => ill_sorted,
            }
        },
        | ContentNode::ThunkType(body) => match minted_comp_type(states, body) {
            | Maybe::Present(body) => {
                Maybe::Present(Minted::ValueType(arena.value_type_thunk(body)))
            },
            | Maybe::Absent(_) => ill_sorted,
        },
        | ContentNode::TypeLift { inner, ref target } => match minted_value_type(states, inner) {
            | Maybe::Present(inner) => Maybe::Present(Minted::ValueType(
                arena.value_type_lift(inner, target.clone()),
            )),
            | Maybe::Absent(_) => ill_sorted,
        },
        | ContentNode::Returner(result) => match minted_value_type(states, result) {
            | Maybe::Present(result) => {
                Maybe::Present(Minted::CompType(arena.comp_type_returner(result)))
            },
            | Maybe::Absent(_) => ill_sorted,
        },
        | ContentNode::Arrow { domain, codomain } => {
            match (
                minted_value_type(states, domain),
                minted_comp_type(states, codomain),
            ) {
                | (Maybe::Present(domain), Maybe::Present(codomain)) => {
                    Maybe::Present(Minted::CompType(arena.comp_type_arrow(domain, codomain)))
                },
                | _ => ill_sorted,
            }
        },
        | ContentNode::Pi { domain, codomain } => {
            match (
                minted_value_type(states, domain),
                minted_comp_type(states, codomain),
            ) {
                | (Maybe::Present(domain), Maybe::Present(codomain)) => {
                    Maybe::Present(Minted::CompType(arena.comp_type_pi(domain, codomain)))
                },
                | _ => ill_sorted,
            }
        },
        | ContentNode::Unresolved(_) => Maybe::Absent(seating::Absent::Unresolved),
        | ContentNode::PathUniverse(..)
        | ContentNode::PrimitiveValue(_)
        | ContentNode::Primitive(..)
        | ContentNode::PathRefl(_)
        | ContentNode::PathProduct(..)
        | ContentNode::PathEquiv { .. }
        | ContentNode::Transport(..)
        | ContentNode::Element { .. }
        | ContentNode::ComputationElement { .. }
        | ContentNode::Variable { .. }
        | ContentNode::Constant(_)
        | ContentNode::Unit
        | ContentNode::Literal(_)
        | ContentNode::Pair(..)
        | ContentNode::Injection(..)
        | ContentNode::Thunk(_)
        | ContentNode::ValueLift { .. }
        | ContentNode::Quote(_)
        | ContentNode::QuoteComputation(_)
        | ContentNode::StaticLambda(_)
        | ContentNode::StaticApplication(..)
        | ContentNode::Lambda(_)
        | ContentNode::Application(..)
        | ContentNode::Return(_)
        | ContentNode::Bind(..)
        | ContentNode::Force(_)
        | ContentNode::Case { .. } => Maybe::Absent(seating::Absent::Unseatable),
    }
}

/// The admission position the item `reference` names takes in `layout`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the position of the item whose own reference is `reference`.
/// - provides: `Unplaced` when no item of the program carries it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a missing abstract reference is refused; repeated keys
///   and skipped positions distinguish successful relocation by occurrence.
/// - witness: `content::tests::an_unmintable_table_is_refused_by_name`
/// - witness: `content::tests::abstract_types_relocate_by_key_and_occurrence`
#[spec(ensures: |ret| match ret {
        | Maybe::Present(position) => layout
            .items
            .iter()
            .zip(&layout.references)
            .any(|(item, named)| item.declaration().constant() == position && named == reference),
        | Maybe::Absent(reason) => {
            reason == seating::Absent::Unplaced
                && !layout.references.iter().any(|named| named == reference)
        },
    })]
fn place(
    layout: &Layout,
    reference: &Reference,
) -> Maybe<gandr_kernel_term::ConstantIndex, seating::Absent>
{
    match layout.ordinal_of(reference) {
        | Maybe::Present(ordinal) => match layout.items.get(usize::from(ordinal)) {
            | Some(item) => Maybe::Present(item.declaration().constant()),
            | None => Maybe::Absent(seating::Absent::Unplaced),
        },
        | Maybe::Absent(_) => Maybe::Absent(seating::Absent::Unplaced),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::body;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use quenchant_shape::shape::Maybe;

    use super::ContentNode;
    use super::Opacity;
    use super::Sort;
    use super::TypeContent;
    use super::encode_item;
    use super::seating;
    use crate::boundary::ItemOrdinal;
    use crate::boundary::NodeIndex;
    use crate::boundary::Occurrence;
    use crate::region::Item;
    use crate::region::ItemKey;
    use crate::region::Program;
    use crate::region::Reference;

    /// The program of one item `it` at position 0 with `signature` and `body`.
    ///
    /// # Specification
    /// - requires: nothing; unresolved ids are allowed.
    /// - ensures: one item at position zero with the supplied two roots.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent allocation, sharing and an unresolved
    ///   body exercise the roots through item encoding.
    /// - witness: `content::tests::content_is_free_of_arena_ids`
    /// - witness: `content::tests::a_shared_node_is_listed_once`
    /// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
    #[spec(ensures: |ret| ret.items().len() == 1
        && ret.items().first().is_some_and(|item| item.declaration().signature() == signature
            && item.declaration().body() == body
            && item.declaration().constant() == ConstantIndex::from(0_usize)))]
    fn single(
        arena: CoreArena,
        signature: Maybe<ValueTypeId, signature::Absent>,
        body: Maybe<ValueId, body::Absent>,
    ) -> Program
    {
        Program::new(arena, vec![Item::new(
            ItemKey::from("it"),
            Declaration::new(
                ConstantIndex::from(0_usize),
                signature,
                body,
                OriginToken::from(0_usize),
            ),
        )])
        .expect("one item ascends")
    }

    /// The integer literal zero.
    ///
    /// # Specification
    /// trivial.
    fn zero() -> Literal
    {
        Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero()))
    }

    /// `U (Integer → F Integer)`, its one `Integer` node shared by domain and
    /// result, built in `arena`.
    ///
    /// # Specification
    /// - requires: the arena has identifier headroom for the four nodes.
    /// - ensures: a thunk of an arrow whose integer domain is also its result.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — content has four entries despite two integer uses,
    ///   and reconstruction in a noisy arena preserves that shared graph.
    /// - witness: `content::tests::a_type_minted_back_has_its_own_content`
    /// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
    #[spec(ensures: |ret| match arena.value_type(ret) {
            | Some(&gandr_core_term::ValueType::Thunk(arrow)) => match arena.comp_type(arrow) {
                | Some(&gandr_core_term::CompType::Arrow { domain, codomain }) => {
                    arena.value_type(domain)
                        == Some(&gandr_core_term::ValueType::Base(BaseType::Integer))
                        && arena.comp_type(codomain)
                            == Some(&gandr_core_term::CompType::Returner(domain))
                },
                | _ => false,
            },
            | _ => false,
        })]
    fn shared_arrow(arena: &mut CoreArena) -> ValueTypeId
    {
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returner);
        arena.value_type_thunk(arrow)
    }

    #[test]
    fn a_type_minted_back_has_its_own_content()
    {
        let mut source = CoreArena::new();
        let ty = shared_arrow(&mut source);
        let program = single(
            source,
            Maybe::Present(ty),
            Maybe::Absent(body::Absent::Hole),
        );
        let content = TypeContent::of_value_type(&program, ty);
        assert_eq!(
            content.nodes().len(),
            4_usize,
            "thunk, arrow, the shared integer once, returner"
        );
        let mut target = CoreArena::new();
        // Unrelated nodes first, so the minted ids differ from the source's.
        let _noise = target.value_type_unit();
        let _noise = target.value_type_base(BaseType::String);
        let mut minted_into = single(
            target,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
        );
        let minted = {
            let (arena, layout) = minted_into.parts_mut();
            content.mint(arena, layout)
        };
        let Maybe::Present(minted) = minted
        else {
            panic!("a type table of admitted formers seats: {minted:?}");
        };
        assert_eq!(
            TypeContent::of_value_type(&minted_into, minted),
            content,
            "the minted type reads back as the table it came from, sharing and all"
        );
    }

    #[test]
    fn an_unmintable_table_is_refused_by_name()
    {
        let level = Level::zero();
        let cases = [
            (
                vec![
                    ContentNode::PathUniverse(NodeIndex::from(1_usize), NodeIndex::from(1_usize)),
                    ContentNode::UnitType,
                ],
                seating::Absent::Unseatable,
            ),
            (
                vec![ContentNode::Product(
                    NodeIndex::from(0_usize),
                    NodeIndex::from(0_usize),
                )],
                seating::Absent::Cyclic,
            ),
            (
                vec![ContentNode::Unresolved(Sort::ValueType)],
                seating::Absent::Unresolved,
            ),
            (
                vec![ContentNode::Abstract(Reference::Item {
                    key: ItemKey::from("elsewhere"),
                    occurrence: Occurrence::from(0_usize),
                })],
                seating::Absent::Unplaced,
            ),
            (
                vec![
                    ContentNode::Returner(NodeIndex::from(1_usize)),
                    ContentNode::Base(BaseType::Integer),
                ],
                seating::Absent::IllSorted,
            ),
            (
                vec![
                    ContentNode::Element {
                        code: NodeIndex::from(1_usize),
                        target: level,
                    },
                    ContentNode::Constant(Reference::Unoccupied),
                ],
                seating::Absent::Unseatable,
            ),
        ];
        for (nodes, expected) in cases {
            let mut program = single(
                CoreArena::new(),
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Absent(body::Absent::Hole),
            );
            let (arena, layout) = program.parts_mut();
            assert_eq!(
                TypeContent::from_nodes(nodes).mint(arena, layout),
                Maybe::Absent(expected),
                "each unmintable table names its reason"
            );
        }
    }

    #[test]
    fn content_is_free_of_arena_ids()
    {
        let build = |noise: usize| {
            let mut arena = CoreArena::new();
            for _ in 0 .. noise {
                let _unused = arena.value_unit();
                let _unused = arena.value_type_unit();
            }
            let ty = arena.value_type_base(BaseType::Integer);
            let literal = arena.value_literal(zero());
            let program = single(arena, Maybe::Present(ty), Maybe::Present(literal));
            encode_item(
                program.arena(),
                program.layout(),
                ItemOrdinal::from(0_usize),
            )
            .content
        };
        let plain = build(0_usize);
        assert_eq!(plain, build(5_usize), "ids differ, content does not");
        assert_eq!(
            plain.nodes(),
            [
                ContentNode::Base(BaseType::Integer),
                ContentNode::Literal(zero())
            ],
            "the signature root first, then the body's"
        );
        assert_eq!(
            plain.reference(),
            &Reference::Item {
                key: ItemKey::from("it"),
                occurrence: Occurrence::from(0_usize),
            },
            "the item is named by key and occurrence, not by position"
        );
    }

    #[test]
    fn a_shared_node_is_listed_once()
    {
        let mut shared = CoreArena::new();
        let literal = shared.value_literal(zero());
        let pair = shared.value_pair(literal, literal);
        let shared = single(
            shared,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(pair),
        );
        let shared =
            encode_item(shared.arena(), shared.layout(), ItemOrdinal::from(0_usize)).content;
        assert_eq!(
            shared.nodes(),
            [
                ContentNode::Pair(NodeIndex::from(1_usize), NodeIndex::from(1_usize)),
                ContentNode::Literal(zero()),
            ],
            "one entry for the shared literal"
        );
        let mut apart = CoreArena::new();
        let first = apart.value_literal(zero());
        let second = apart.value_literal(zero());
        let pair = apart.value_pair(first, second);
        let apart = single(
            apart,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(pair),
        );
        let apart = encode_item(apart.arena(), apart.layout(), ItemOrdinal::from(0_usize)).content;
        assert_eq!(apart.nodes().len(), 3_usize, "two literals, two entries");
        assert_ne!(shared, apart, "sharing is part of the content");
    }

    #[test]
    fn an_unresolved_id_makes_the_item_opaque()
    {
        let mut larger = CoreArena::new();
        let _first = larger.value_unit();
        let foreign = larger.value_unit();
        let program = single(
            CoreArena::new(),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(foreign),
        );
        let content = encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        )
        .content;
        assert_eq!(
            content.nodes(),
            [ContentNode::Unresolved(Sort::Value)],
            "the id is listed by its sort"
        );
        assert_eq!(content.opacity(), Opacity::Opaque, "and the item is opaque");
    }

    #[test]
    fn a_signature_renumbers_to_its_own_type_content()
    {
        let mut arena = CoreArena::new();
        let ty = shared_arrow(&mut arena);
        let literal = arena.value_literal(zero());
        let returned = arena.computation_return(literal);
        let lambda = arena.computation_lambda(returned);
        let thunk = arena.value_thunk(lambda);
        let program = single(arena, Maybe::Present(ty), Maybe::Present(thunk));
        let content = encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        )
        .content;
        let interleaved: Vec<&ContentNode> = content.nodes().iter().collect();
        assert!(
            matches!(interleaved.get(1), Some(&&ContentNode::Thunk(_))),
            "the body's root is discovered before the signature's children"
        );
        assert_eq!(
            content.signature_type(),
            Maybe::Present(TypeContent::of_value_type(&program, ty)),
            "the signature renumbered from its root is the type encoded alone"
        );
    }

    #[test]
    fn renumbering_closes_dangling_and_cyclic_tables()
    {
        let index = NodeIndex::from;
        let nodes = [
            ContentNode::UnitType,
            ContentNode::Product(index(3_usize), index(3_usize)),
            ContentNode::Abstract(Reference::Unoccupied),
            ContentNode::ThunkType(index(4_usize)),
            ContentNode::Returner(index(1_usize)),
        ];
        assert_eq!(super::renumber(&nodes, index(1_usize)), [
            ContentNode::Product(index(1_usize), index(1_usize)),
            ContentNode::ThunkType(index(2_usize)),
            ContentNode::Returner(index(0_usize)),
        ]);
        assert_eq!(super::renumber(&nodes, index(2_usize)), [
            ContentNode::Abstract(Reference::Unoccupied),
        ]);
        let dangling = [ContentNode::Case {
            scrutinee: index(usize::MAX),
            on_left: index(0_usize),
            on_right: index(usize::MAX),
        }];
        assert_eq!(super::renumber(&dangling, index(0_usize)), [
            ContentNode::Case {
                scrutinee: index(1_usize),
                on_left: index(0_usize),
                on_right: index(1_usize),
            },
            ContentNode::Unresolved(Sort::Value),
        ]);
        assert_eq!(super::renumber(&nodes, index(usize::MAX)), [
            ContentNode::Unresolved(Sort::Value),
        ]);
    }

    #[test]
    fn malformed_type_tables_fail_by_structure()
    {
        let index = NodeIndex::from;
        let cases = [
            vec![],
            vec![
                ContentNode::Product(index(1_usize), index(usize::MAX)),
                ContentNode::UnitType,
            ],
            vec![
                ContentNode::Product(index(1_usize), index(2_usize)),
                ContentNode::Returner(index(2_usize)),
                ContentNode::UnitType,
            ],
            vec![
                ContentNode::Arrow {
                    domain: index(1_usize),
                    codomain: index(1_usize),
                },
                ContentNode::UnitType,
            ],
        ];
        for nodes in cases {
            let mut program = single(
                CoreArena::new(),
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Absent(body::Absent::Hole),
            );
            let (arena, layout) = program.parts_mut();
            assert_eq!(
                TypeContent::from_nodes(nodes).mint(arena, layout),
                Maybe::Absent(seating::Absent::IllSorted)
            );
        }
    }

    #[test]
    fn abstract_types_relocate_by_key_and_occurrence()
    {
        let items = [17_usize, 42_usize]
            .into_iter()
            .map(|position| {
                Item::new(
                    ItemKey::from("repeated"),
                    Declaration::new(
                        ConstantIndex::from(position),
                        Maybe::Absent(signature::Absent::Unsigned),
                        Maybe::Absent(body::Absent::Hole),
                        OriginToken::from(position),
                    ),
                )
            })
            .collect();
        let mut program = Program::new(CoreArena::new(), items).expect("ascending positions");
        let named = Reference::Item {
            key: ItemKey::from("repeated"),
            occurrence: Occurrence::from(1_usize),
        };
        let content = TypeContent::from_nodes(vec![ContentNode::Abstract(named)]);
        let minted = {
            let (arena, layout) = program.parts_mut();
            content.mint(arena, layout)
        };
        let Maybe::Present(id) = minted
        else {
            panic!("an existing occurrence must place: {minted:?}");
        };
        assert_eq!(
            program.arena().value_type(id),
            Some(&gandr_core_term::ValueType::Abstract(ConstantIndex::from(
                42_usize
            )))
        );
        assert_eq!(TypeContent::of_value_type(&program, id), content);
        let absent = TypeContent::from_nodes(vec![ContentNode::Abstract(Reference::Item {
            key: ItemKey::from("repeated"),
            occurrence: Occurrence::from(2_usize),
        })]);
        let (arena, layout) = program.parts_mut();
        assert_eq!(
            absent.mint(arena, layout),
            Maybe::Absent(seating::Absent::Unplaced)
        );
    }
}
