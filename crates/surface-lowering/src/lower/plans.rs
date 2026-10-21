//! Each node's plan, the plans of a suspended lowering's nodes shared by every
//! lowering resumed from it. A lowering suspended after an import closure
//! holds a plan for each of the closure's nodes; each lowering resumed from it
//! reads them, and plans the document's nodes after them. [`Plans`] keeps the
//! suspended plans behind one `Arc`, so a resumed lowering copies none of
//! them, and keeps a plan written at a shared node apart, copied from the
//! shared plan the first time it is written.
//!
//! # Witnesses
//! - `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
//! - `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::NodeCount;
use gandr_surface_syntax::NodeIndex;

use super::Plan;

/// Each node's plan, by the node's position: the shared plans of the nodes a
/// suspended lowering read, any of them written since, and the plans of the
/// nodes read after them.
///
/// # Specification
/// - ensures: the plan at a position is the one last written there, and
///   [`Plan::Unplanned`] for a position never written; a clone holds the same
///   plans, and a write to either is not seen by the other.
/// - provides: the lowering's per-node plan table.
/// - fails: none as a data value.
/// - panics: none as a data value.
/// - executable: none — the methods state the table's reading.
///
/// # Adequacy
/// - hypothesis: L3 — as the module's witnesses.
/// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[derive(Clone, Debug, Default)]
pub(super) struct Plans
{
    /// The plans [`Self::share`] shared, by node.
    shared: Arc<[Plan]>,
    /// The shared nodes written since they were shared, each with its plan.
    written: BTreeMap<NodeIndex, Plan>,
    /// The plans of the nodes after the shared ones, by node.
    own: Vec<Plan>,
}

impl Plans
{
    /// `count` nodes, none planned.
    ///
    /// # Specification
    /// - ensures: [`Self::count`] is `count`, and every plan
    ///   [`Plan::Unplanned`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
    #[spec(ensures: |ret| ret.count() == count && ret.iter().all(|plan| *plan == Plan::Unplanned))]
    #[inline]
    pub(super) fn unplanned(count: NodeCount) -> Self
    {
        let mut own = Vec::new();
        own.resize(usize::from(count), Plan::Unplanned);
        Self {
            shared: Arc::default(),
            written: BTreeMap::new(),
            own,
        }
    }

    /// How many nodes the table holds a plan for.
    ///
    /// # Specification
    /// - ensures: the shared plans and the own ones together.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
    #[spec(ensures: |ret| usize::from(ret) == self.shared.len().saturating_add(self.own.len()))]
    #[inline]
    pub(super) fn count(&self) -> NodeCount
    {
        NodeCount::from(self.shared.len().saturating_add(self.own.len()))
    }

    /// The plan at `at`, or nothing past the last node.
    ///
    /// # Specification
    /// - ensures: a shared node's plan as written since it was shared, else as
    ///   shared; a node after them its own plan; nothing past [`Self::count`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
    #[spec(ensures: |ret| ret.is_some() == (usize::from(at) < usize::from(self.count())))]
    #[inline]
    pub(super) fn get(
        &self,
        at: NodeIndex,
    ) -> Option<&Plan>
    {
        let position = usize::from(at);
        position.checked_sub(self.shared.len()).map_or_else(
            || self.written.get(&at).or_else(|| self.shared.get(position)),
            |own| self.own.get(own),
        )
    }

    /// The plan at `at` to write, or nothing past the last node: a shared
    /// node's plan is first copied apart, so no other table sharing it sees
    /// the write.
    ///
    /// # Specification
    /// - ensures: what [`Self::get`] reads at `at`, writable; the other
    ///   positions' plans unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
    #[spec(
        captures: count = self.count(),
        ensures: |ret| ret.is_some() == (usize::from(at) < usize::from(count)),
    )]
    #[inline]
    pub(super) fn get_mut(
        &mut self,
        at: NodeIndex,
    ) -> Option<&mut Plan>
    {
        let position = usize::from(at);
        if let Some(own) = position.checked_sub(self.shared.len()) {
            return self.own.get_mut(own);
        }
        let shared = self.shared.get(position)?;
        Some(self.written.entry(at).or_insert_with(|| shared.clone()))
    }

    /// Every node's plan, in node order.
    ///
    /// # Specification
    /// - ensures: [`Self::count`] plans, the one at each position what
    ///   [`Self::get`] reads there.
    /// - panics: none.
    /// - executable: none — an iterator; the witness reads it against
    ///   [`Self::get`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
    #[inline]
    pub(super) fn iter(&self) -> impl Iterator<Item = &Plan>
    {
        self.shared
            .iter()
            .enumerate()
            .map(|(position, plan)| self.written.get(&NodeIndex::from(position)).unwrap_or(plan))
            .chain(self.own.iter())
    }

    /// Hold `count` nodes, the ones added unplanned.
    ///
    /// # Specification
    /// - requires: `count` is at least [`Self::count`].
    /// - ensures: [`Self::count`] is `count`; the plans held before kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(
        requires: usize::from(count) >= usize::from(self.count()),
        ensures: self.count() == count,
    )]
    #[inline]
    pub(super) fn widen(
        &mut self,
        count: NodeCount,
    )
    {
        let own = usize::from(count).saturating_sub(self.shared.len());
        self.own.resize(own, Plan::Unplanned);
    }

    /// Share every plan, so a clone copies none of them.
    ///
    /// # Specification
    /// - ensures: every position's plan kept; none written apart and none held
    ///   as the table's own.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Plans`].
    /// - witness: `lower::plans::tests::a_write_to_a_shared_plan_is_the_writer_s_own_776`
    #[spec(
        captures: count = self.count(),
        ensures: self.count() == count && self.written.is_empty() && self.own.is_empty(),
    )]
    #[inline]
    pub(super) fn share(&mut self)
    {
        if self.own.is_empty() && self.written.is_empty() {
            return;
        }
        let own = core::mem::take(&mut self.own);
        let plans: Vec<Plan> = if self.shared.is_empty() {
            own
        }
        else {
            let written = core::mem::take(&mut self.written);
            let mut plans = self.shared.to_vec();
            for (at, plan) in written {
                if let Some(held) = plans.get_mut(usize::from(at)) {
                    *held = plan;
                }
            }
            plans.extend(own);
            plans
        };
        self.shared = Arc::from(plans);
    }
}

#[cfg(test)]
mod tests
{
    use alloc::sync::Arc;
    use alloc::vec::Vec;

    use gandr_surface_syntax::NodeCount;
    use gandr_surface_syntax::NodeIndex;

    use super::Plan;
    use super::Plans;

    /// #776: a lowering resumed after its closure shares the closure's plans
    /// with the suspended lowering rather than copying them, so a plan one of
    /// them writes at a shared node is its own: the other still reads the
    /// shared plan. Sharing keeps every plan where it was, and widening adds
    /// unplanned nodes after them.
    #[test]
    fn a_write_to_a_shared_plan_is_the_writer_s_own_776()
    {
        let mut suspended = Plans::unplanned(NodeCount::from(3_usize));
        *suspended.get_mut(NodeIndex::from(1_usize)).expect("node 1") = Plan::Break;
        suspended.share();
        assert_eq!(suspended.count(), NodeCount::from(3_usize));
        assert_eq!(suspended.iter().collect::<Vec<_>>(), [
            &Plan::Unplanned,
            &Plan::Break,
            &Plan::Unplanned
        ],);

        let mut resumed = suspended.clone();
        assert!(Arc::ptr_eq(&resumed.shared, &suspended.shared));
        resumed.widen(NodeCount::from(5_usize));
        *resumed.get_mut(NodeIndex::from(0_usize)).expect("node 0") = Plan::Break;
        *resumed.get_mut(NodeIndex::from(4_usize)).expect("node 4") = Plan::Break;
        *resumed.get_mut(NodeIndex::from(1_usize)).expect("node 1") = Plan::Unplanned;

        assert_eq!(resumed.iter().collect::<Vec<_>>(), [
            &Plan::Break,
            &Plan::Unplanned,
            &Plan::Unplanned,
            &Plan::Unplanned,
            &Plan::Break
        ],);
        assert_eq!(resumed.get(NodeIndex::from(0_usize)), Some(&Plan::Break));
        assert_eq!(resumed.get(NodeIndex::from(5_usize)), None);
        assert!(Arc::ptr_eq(&resumed.shared, &suspended.shared));
        assert_eq!(suspended.iter().collect::<Vec<_>>(), [
            &Plan::Unplanned,
            &Plan::Break,
            &Plan::Unplanned
        ],);
        assert_eq!(suspended.get(NodeIndex::from(3_usize)), None);

        resumed.share();
        assert_eq!(resumed.iter().collect::<Vec<_>>(), [
            &Plan::Break,
            &Plan::Unplanned,
            &Plan::Unplanned,
            &Plan::Unplanned,
            &Plan::Break
        ],);
    }
}
