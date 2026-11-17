//! The node each rewritten node stands for, read back from rewrite traces.

use alloc::collections::BTreeMap;

use anodized::spec;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::rewrite::Carried;

/// The node each node a rewrite put in place stands for, family by family.
///
/// A traced rewrite reports each node it changed beside the node it changed it
/// from ([`Carried`]). A reader that keeps a table beside the arena, an origin
/// or a written term, reads a rewritten node's entry from the node it stands
/// for here. A node reported from several sources stands for the first.
/// [`Self::record_through`] reads a later trace through the nodes the table
/// holds, so a chain of rewrites stands for its first node.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each map sends a rewritten node to the node it stands for.
/// - executable: none — the table holds no arena to check either id against.
///
/// # Adequacy
/// - hypothesis: L3 — a node reported from two sources stands for the first,
///   one report keeps a chain apart, and a report read through the table stands
///   for the chain's first node.
/// - witness: `sources::tests::a_rewrite_stands_for_its_first_source_and_a_later_one_reads_through`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Sources
{
    /// The value each rewritten value stands for.
    values: BTreeMap<ValueId, ValueId>,
    /// The computation each rewritten computation stands for.
    computations: BTreeMap<ComputationId, ComputationId>,
    /// The value type each rewritten value type stands for.
    value_types: BTreeMap<ValueTypeId, ValueTypeId>,
    /// The computation type each rewritten computation type stands for.
    comp_types: BTreeMap<CompTypeId, CompTypeId>,
}

impl Sources
{
    /// The table that holds no source: every node stands for itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            values: BTreeMap::new(),
            computations: BTreeMap::new(),
            value_types: BTreeMap::new(),
            comp_types: BTreeMap::new(),
        }
    }

    /// The sources `carried` reports: each node it reports rewritten beside
    /// the first node it reports it rewritten from.
    ///
    /// # Specification
    /// - ensures: each node `carried` reports rewritten stands for the first
    ///   node a pair rewrites it from, as reported, with no pair read through
    ///   another.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Sources`].
    /// - witness: `sources::tests::a_rewrite_stands_for_its_first_source_and_a_later_one_reads_through`
    #[spec(ensures: |ret| carried.iter().all(|&pair| match pair {
        Carried::Value(_, rewritten) => ret.values.contains_key(&rewritten),
        Carried::Computation(_, rewritten) => ret.computations.contains_key(&rewritten),
        Carried::ValueType(_, rewritten) => ret.value_types.contains_key(&rewritten),
        Carried::CompType(_, rewritten) => ret.comp_types.contains_key(&rewritten),
    }))]
    #[inline]
    #[must_use]
    pub fn of(carried: &[Carried]) -> Self
    {
        let mut sources = Self::default();
        for &pair in carried {
            match pair {
                Carried::Value(held, rewritten) => {
                    let _first = sources.values.entry(rewritten).or_insert(held);
                },
                Carried::Computation(held, rewritten) => {
                    let _first = sources.computations.entry(rewritten).or_insert(held);
                },
                Carried::ValueType(held, rewritten) => {
                    let _first = sources.value_types.entry(rewritten).or_insert(held);
                },
                Carried::CompType(held, rewritten) => {
                    let _first = sources.comp_types.entry(rewritten).or_insert(held);
                },
            }
        }
        sources
    }

    /// Read `carried`, a trace of rewrites made after the ones this table
    /// holds, through this table: each node it reports rewritten stands for
    /// what the node it is rewritten from stands for here.
    ///
    /// # Specification
    /// - requires: `carried` lists its pairs in the order the rewrites made
    ///   them.
    /// - ensures: each node `carried` reports rewritten has a source. A node
    ///   reported twice, or held before, keeps its first source.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Sources`].
    /// - witness: `sources::tests::a_rewrite_stands_for_its_first_source_and_a_later_one_reads_through`
    #[spec(ensures: carried.iter().all(|&pair| match pair {
        Carried::Value(_, rewritten) => self.values.contains_key(&rewritten),
        Carried::Computation(_, rewritten) => self.computations.contains_key(&rewritten),
        Carried::ValueType(_, rewritten) => self.value_types.contains_key(&rewritten),
        Carried::CompType(_, rewritten) => self.comp_types.contains_key(&rewritten),
    }))]
    #[inline]
    pub fn record_through(
        &mut self,
        carried: &[Carried],
    )
    {
        for &pair in carried {
            match pair {
                Carried::Value(held, rewritten) => {
                    let source = self.value(held);
                    let _kept = self.values.entry(rewritten).or_insert(source);
                },
                Carried::Computation(held, rewritten) => {
                    let source = self.computation(held);
                    let _kept = self.computations.entry(rewritten).or_insert(source);
                },
                Carried::ValueType(held, rewritten) => {
                    let source = self.value_type(held);
                    let _kept = self.value_types.entry(rewritten).or_insert(source);
                },
                Carried::CompType(held, rewritten) => {
                    let source = self.comp_type(held);
                    let _kept = self.comp_types.entry(rewritten).or_insert(source);
                },
            }
        }
    }

    /// The value `at` stands for, or `at` when no rewrite put it in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        at: ValueId,
    ) -> ValueId
    {
        self.values.get(&at).copied().unwrap_or(at)
    }

    /// The computation `at` stands for, or `at` when no rewrite put it in
    /// place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn computation(
        &self,
        at: ComputationId,
    ) -> ComputationId
    {
        self.computations.get(&at).copied().unwrap_or(at)
    }

    /// The value type `at` stands for, or `at` when no rewrite put it in
    /// place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value_type(
        &self,
        at: ValueTypeId,
    ) -> ValueTypeId
    {
        self.value_types.get(&at).copied().unwrap_or(at)
    }

    /// The computation type `at` stands for, or `at` when no rewrite put it in
    /// place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn comp_type(
        &self,
        at: CompTypeId,
    ) -> CompTypeId
    {
        self.comp_types.get(&at).copied().unwrap_or(at)
    }

    /// Each rewritten value beside the value it stands for, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn values(&self) -> &BTreeMap<ValueId, ValueId>
    {
        &self.values
    }

    /// Each rewritten computation beside the computation it stands for,
    /// ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn computations(&self) -> &BTreeMap<ComputationId, ComputationId>
    {
        &self.computations
    }

    /// Each rewritten value type beside the value type it stands for,
    /// ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn value_types(&self) -> &BTreeMap<ValueTypeId, ValueTypeId>
    {
        &self.value_types
    }

    /// Each rewritten computation type beside the computation type it stands
    /// for, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn comp_types(&self) -> &BTreeMap<CompTypeId, CompTypeId>
    {
        &self.comp_types
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::Sources;
    use crate::arena::CoreArena;
    use crate::rewrite::Carried;

    #[test]
    fn a_rewrite_stands_for_its_first_source_and_a_later_one_reads_through()
    {
        let mut arena = CoreArena::new();
        let [written, entry, crossed, elaborated, updated, kept] =
            [0_usize; 6].map(|_| arena.value_unit());
        let mut sources = Sources::of(&[
            Carried::Value(written, crossed),
            Carried::Value(entry, crossed),
            Carried::Value(crossed, elaborated),
        ]);
        assert_eq!(
            sources.value(crossed),
            written,
            "a node reported from two sources stands for the first"
        );
        assert_eq!(
            sources.value(elaborated),
            crossed,
            "one report reads each pair as reported"
        );
        assert_eq!(
            sources.value(kept),
            kept,
            "a node no rewrite reports stands for itself"
        );
        sources.record_through(&[
            Carried::Value(elaborated, updated),
            Carried::Value(kept, crossed),
        ]);
        assert_eq!(
            sources.value(updated),
            crossed,
            "a later report reads its source through the table"
        );
        assert_eq!(
            sources.value(crossed),
            written,
            "a later report keeps the source a node holds"
        );
        assert_eq!(
            sources.values().keys().copied().collect::<Vec<_>>(),
            [crossed, elaborated, updated],
            "the table holds the rewritten nodes alone"
        );
    }
}
