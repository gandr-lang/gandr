//! A per-node table whose cells a suspended lowering shares with every
//! lowering resumed from it. A lowering suspended after an import closure
//! holds a cell for each of the closure's nodes in each of its per-node
//! tables; each lowering resumed from it reads them, and adds the document's
//! nodes after them. [`NodeTable`] keeps the suspended cells behind one `Arc`,
//! so a resumed lowering copies none of them, and keeps a cell written at a
//! shared node apart, copied from the shared cell the first time it is
//! written.
//!
//! # Witnesses
//! - `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
//! - `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::NodeCount;
use gandr_surface_syntax::NodeIndex;

/// Each node's cell, by the node's position: the shared cells of the nodes a
/// suspended lowering read, any of them written since, and the cells of the
/// nodes read after them.
///
/// # Specification
/// - ensures: the cell at a position is the one last written there, and the
///   fill cell for a position never written; a clone holds the same cells, and
///   a write to either is not seen by the other.
/// - provides: the lowering's per-node tables.
/// - fails: none as a data value.
/// - panics: none as a data value.
/// - executable: none — the methods state the table's reading.
///
/// # Adequacy
/// - hypothesis: L3 — as the module's witnesses.
/// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[derive(Clone, Debug)]
pub struct NodeTable<Cell>
{
    /// The cells [`Self::share`] shared, by node.
    shared: Arc<[Cell]>,
    /// The shared nodes written since they were shared, each with its cell.
    written: BTreeMap<NodeIndex, Cell>,
    /// The cells of the nodes after the shared ones, by node.
    own: Vec<Cell>,
}

impl<Cell: Clone> NodeTable<Cell>
{
    /// `count` nodes, each holding `cell`.
    ///
    /// # Specification
    /// - ensures: [`Self::count`] is `count`, and every cell `cell`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(ensures: |ret| ret.count() == count)]
    #[inline]
    pub fn filled(
        count: NodeCount,
        cell: Cell,
    ) -> Self
    {
        let mut own = Vec::new();
        own.resize(usize::from(count), cell);
        Self {
            shared: Arc::from(Vec::new()),
            written: BTreeMap::new(),
            own,
        }
    }

    /// How many nodes the table holds a cell for.
    ///
    /// # Specification
    /// - ensures: the shared cells and the own ones together.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(ensures: |ret| usize::from(ret) == self.shared.len().saturating_add(self.own.len()))]
    #[inline]
    pub fn count(&self) -> NodeCount
    {
        NodeCount::from(self.shared.len().saturating_add(self.own.len()))
    }

    /// The cell at `at`, or nothing past the last node.
    ///
    /// # Specification
    /// - ensures: a shared node's cell as written since it was shared, else as
    ///   shared; a node after them its own cell; nothing past [`Self::count`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(ensures: |ret| ret.is_some() == (usize::from(Into::<NodeIndex>::into(at)) < usize::from(self.count())))]
    #[inline]
    pub fn get<At>(
        &self,
        at: At,
    ) -> Option<&Cell>
    where
        At: Copy + Into<NodeIndex>,
    {
        let at = at.into();
        let position = usize::from(at);
        position.checked_sub(self.shared.len()).map_or_else(
            || self.written.get(&at).or_else(|| self.shared.get(position)),
            |own| self.own.get(own),
        )
    }

    /// The cell at `at` to write, or nothing past the last node: a shared
    /// node's cell is first copied apart, so no other table sharing it sees
    /// the write.
    ///
    /// # Specification
    /// - ensures: what [`Self::get`] reads at `at`, writable; the other
    ///   positions' cells unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(
        captures: count = self.count(),
        ensures: |ret| ret.is_some() == (usize::from(Into::<NodeIndex>::into(at)) < usize::from(count)),
    )]
    #[inline]
    pub fn get_mut<At>(
        &mut self,
        at: At,
    ) -> Option<&mut Cell>
    where
        At: Copy + Into<NodeIndex>,
    {
        let at = at.into();
        let position = usize::from(at);
        if let Some(own) = position.checked_sub(self.shared.len()) {
            return self.own.get_mut(own);
        }
        let shared = self.shared.get(position)?;
        Some(self.written.entry(at).or_insert_with(|| shared.clone()))
    }

    /// Every node's cell, in node order.
    ///
    /// # Specification
    /// - ensures: [`Self::count`] cells, the one at each position what
    ///   [`Self::get`] reads there.
    /// - panics: none.
    /// - executable: none — an iterator; the witness reads it against
    ///   [`Self::get`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Cell>
    {
        self.shared
            .iter()
            .enumerate()
            .map(|(position, cell)| self.written.get(&NodeIndex::from(position)).unwrap_or(cell))
            .chain(self.own.iter())
    }

    /// Hold `count` nodes, the ones added holding `cell`.
    ///
    /// # Specification
    /// - requires: `count` is at least [`Self::count`].
    /// - ensures: [`Self::count`] is `count`; the cells held before kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(
        requires: usize::from(count) >= usize::from(self.count()),
        ensures: self.count() == count,
    )]
    #[inline]
    pub fn widen(
        &mut self,
        count: NodeCount,
        cell: Cell,
    )
    {
        let own = usize::from(count).saturating_sub(self.shared.len());
        self.own.resize(own, cell);
    }

    /// Share every cell, so a clone copies none of them.
    ///
    /// # Specification
    /// - ensures: every position's cell kept; none written apart and none held
    ///   as the table's own.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(
        captures: count = self.count(),
        ensures: self.count() == count && self.written.is_empty() && self.own.is_empty(),
    )]
    #[inline]
    pub fn share(&mut self)
    {
        if self.own.is_empty() && self.written.is_empty() {
            return;
        }
        let own = core::mem::take(&mut self.own);
        let cells: Vec<Cell> = if self.shared.is_empty() {
            own
        }
        else {
            let written = core::mem::take(&mut self.written);
            let mut cells = self.shared.to_vec();
            for (at, cell) in written {
                if let Some(held) = cells.get_mut(usize::from(at)) {
                    *held = cell;
                }
            }
            cells.extend(own);
            cells
        };
        self.shared = Arc::from(cells);
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::sync::Arc;

    use gandr_surface_syntax::NodeCount;
    use gandr_surface_syntax::NodeIndex;

    use super::NodeTable;

    /// #776: a lowering resumed after its closure shares the closure's cells
    /// with the suspended lowering rather than copying them, so a cell one of
    /// them writes at a shared node is its own: the other still reads the
    /// shared cell. Sharing keeps every cell where it was, and widening adds
    /// filled nodes after them.
    #[test]
    fn a_write_to_a_shared_cell_is_the_writer_s_own_776()
    {
        let cells = |table: &NodeTable<char>| table.iter().copied().collect::<String>();
        let mut suspended = NodeTable::filled(NodeCount::from(3_usize), '-');
        *suspended.get_mut(NodeIndex::from(1_usize)).expect("node 1") = 'b';
        suspended.share();
        assert_eq!(suspended.count(), NodeCount::from(3_usize));
        assert_eq!("-b-", cells(&suspended));

        let mut resumed = suspended.clone();
        assert!(Arc::ptr_eq(&resumed.shared, &suspended.shared));
        resumed.widen(NodeCount::from(5_usize), '-');
        *resumed.get_mut(NodeIndex::from(0_usize)).expect("node 0") = 'a';
        *resumed.get_mut(NodeIndex::from(4_usize)).expect("node 4") = 'e';
        *resumed.get_mut(NodeIndex::from(1_usize)).expect("node 1") = '-';

        assert_eq!("a---e", cells(&resumed));
        assert_eq!(resumed.get(NodeIndex::from(0_usize)), Some(&'a'));
        assert_eq!(resumed.get(NodeIndex::from(5_usize)), None);
        assert!(
            Arc::ptr_eq(&resumed.shared, &suspended.shared),
            "the writes leave the shared cells shared"
        );
        assert_eq!(
            "-b-",
            cells(&suspended),
            "and unseen by the suspended table"
        );
        assert_eq!(suspended.get(NodeIndex::from(3_usize)), None);

        resumed.share();
        assert_eq!("a---e", cells(&resumed), "sharing keeps every cell");
    }
}
