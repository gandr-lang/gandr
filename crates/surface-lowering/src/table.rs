//! A per-node table whose cells a suspended lowering shares with every
//! lowering resumed from it. A lowering suspended after an import closure
//! holds a cell for each of the closure's nodes in each of its per-node
//! tables; each lowering resumed from it reads them, and adds the document's
//! blocks after them. [`NodeTable`] keeps the suspended cells behind one `Arc`,
//! so a resumed lowering copies none of them, and keeps a cell written at a
//! shared node apart, copied from the shared cell the first time it is
//! written. A node's cell is named by its layout block and its offset there;
//! the table keeps each block's cells side by side, so a top-level form's
//! descendants hold one run of cells.
//!
//! # Witnesses
//! - `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
//! - `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::BlockOffset;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeCount;
use gandr_surface_syntax::NodeIndex;

/// Each node's cell, by the node's block and its offset there: the shared
/// cells of the nodes a suspended lowering read, any of them written since,
/// and the cells of the blocks read after them.
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
    /// Where each block's cells start among the table's cells, in block
    /// order.
    starts: Vec<usize>,
    /// The cells [`Self::share`] shared, block after block.
    shared: Arc<[Cell]>,
    /// The shared nodes written since they were shared, each with its cell.
    written: BTreeMap<NodeIndex, Cell>,
    /// The cells of the blocks after the shared ones, block after block.
    own: Vec<Cell>,
}

impl<Cell: Clone> NodeTable<Cell>
{
    /// A block of each length of `blocks`, every cell `cell`.
    ///
    /// # Specification
    /// - ensures: one block per length of `blocks`, each that long, and every
    ///   cell `cell`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(ensures: |ret| ret.shared.is_empty()
        && ret.written.is_empty()
        && ret.starts.first().is_none_or(|&start| start == 0_usize))]
    #[inline]
    pub fn filled<Blocks>(
        blocks: Blocks,
        cell: Cell,
    ) -> Self
    where
        Blocks: IntoIterator<Item = NodeCount>,
    {
        let mut table = Self {
            starts: Vec::new(),
            shared: Arc::from(Vec::new()),
            written: BTreeMap::new(),
            own: Vec::new(),
        };
        table.widen(blocks, cell);
        table
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

    /// The first block the table holds no cells for: the count of its
    /// blocks.
    ///
    /// # Specification
    /// - ensures: the blocks the table holds, counted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(ensures: |ret| usize::from(ret) == self.starts.len())]
    #[inline]
    pub fn blocks(&self) -> LayoutBlock
    {
        LayoutBlock::from(self.starts.len())
    }

    /// How many cells `block` holds; none for a block the table does not hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn block_cells(
        &self,
        block: LayoutBlock,
    ) -> NodeCount
    {
        let index = usize::from(block);
        let Some(&start) = self.starts.get(index)
        else {
            return NodeCount::from(0_usize);
        };
        let end = self
            .starts
            .get(index.saturating_add(1))
            .copied()
            .unwrap_or_else(|| usize::from(self.count()));
        NodeCount::from(end.saturating_sub(start))
    }

    /// Where the cell at `at` lies among the table's cells, as the count of
    /// cells before it, or nothing for a block or an offset the table does not
    /// hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn flat(
        &self,
        at: NodeIndex,
    ) -> Option<NodeCount>
    {
        let start = *self.starts.get(usize::from(at.block()))?;
        let offset = usize::from(at.offset());
        (offset < usize::from(self.block_cells(at.block())))
            .then(|| NodeCount::from(start.saturating_add(offset)))
    }

    /// The cell at `at`, or nothing for a node the table holds no cell for.
    ///
    /// # Specification
    /// - ensures: a shared node's cell as written since it was shared, else as
    ///   shared; a node of a later block its own cell; nothing for a block or
    ///   an offset the table does not hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[spec(ensures: |ret| ret.is_some() == self.flat(Into::<NodeIndex>::into(at)).is_some())]
    #[inline]
    pub fn get<At>(
        &self,
        at: At,
    ) -> Option<&Cell>
    where
        At: Copy + Into<NodeIndex>,
    {
        let at = at.into();
        let flat = usize::from(self.flat(at)?);
        flat.checked_sub(self.shared.len()).map_or_else(
            || self.written.get(&at).or_else(|| self.shared.get(flat)),
            |own| self.own.get(own),
        )
    }

    /// The cell at `at` to write, or nothing for a node the table holds no
    /// cell for: a shared node's cell is first copied apart, so no other table
    /// sharing it sees the write.
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
        captures: held = self.get(at).is_some(),
        ensures: |ret| ret.is_some() == held,
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
        let flat = usize::from(self.flat(at)?);
        if let Some(own) = flat.checked_sub(self.shared.len()) {
            return self.own.get_mut(own);
        }
        let shared = self.shared.get(flat)?;
        Some(self.written.entry(at).or_insert_with(|| shared.clone()))
    }

    /// Every node's position and cell, in node order.
    ///
    /// # Specification
    /// - ensures: [`Self::count`] cells, the one at each position what
    ///   [`Self::get`] reads there, block by block.
    /// - panics: none.
    /// - executable: none — an iterator; the witness reads it against
    ///   [`Self::get`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `table::tests::a_write_to_a_shared_cell_is_the_writer_s_own_776`
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (NodeIndex, &Cell)>
    {
        let count = usize::from(self.count());
        let shared = self.shared.len();
        self.starts
            .iter()
            .enumerate()
            .flat_map(move |(block, &start)| {
                let end = self
                    .starts
                    .get(block.saturating_add(1))
                    .copied()
                    .unwrap_or(count);
                // A block lies wholly among the shared cells or wholly among
                // the own ones: sharing takes every block and widening adds
                // whole blocks.
                let (cells, written) = start.checked_sub(shared).map_or_else(
                    || {
                        (
                            self.shared.get(start .. end).unwrap_or_default(),
                            (!self.written.is_empty()).then_some(&self.written),
                        )
                    },
                    |own| {
                        (
                            self.own
                                .get(own .. end.saturating_sub(shared))
                                .unwrap_or_default(),
                            None,
                        )
                    },
                );
                cells.iter().enumerate().map(move |(offset, cell)| {
                    let at = NodeIndex::at(LayoutBlock::from(block), BlockOffset::from(offset));
                    (
                        at,
                        written.and_then(|written| written.get(&at)).unwrap_or(cell),
                    )
                })
            })
    }

    /// Hold a block of each length of `blocks`, the cells added holding
    /// `cell`.
    ///
    /// # Specification
    /// - requires: `blocks` starts with the lengths of the blocks the table
    ///   holds.
    /// - ensures: one block per length of `blocks`, each that long; the cells
    ///   held before kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`NodeTable`].
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    #[spec(
        captures: held = self.count(),
        ensures: usize::from(self.count()) >= usize::from(held),
    )]
    #[inline]
    pub fn widen<Blocks>(
        &mut self,
        blocks: Blocks,
        cell: Cell,
    ) where
        Blocks: IntoIterator<Item = NodeCount>,
    {
        let held = self.starts.len();
        let mut count = usize::from(self.count());
        for length in blocks.into_iter().skip(held) {
            self.starts.push(count);
            count = count.saturating_add(usize::from(length));
        }
        self.own
            .resize(count.saturating_sub(self.shared.len()), cell);
    }

    /// Write `cell` into every cell of `block`, or nothing for a block the
    /// table does not hold.
    ///
    /// # Specification
    /// - ensures: every cell of `block` is `cell`; every other cell unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block among the own cells and one among the shared
    ///   cells are filled, and the blocks beside each keep their cells.
    /// - witness: `table::tests::filling_a_block_writes_its_cells_alone`
    #[spec(
        captures: wanted = cell.clone(),
        ensures: (0_usize .. usize::from(self.block_cells(block))).all(|offset| {
            self.get(NodeIndex::at(block, BlockOffset::from(offset))) == Some(&wanted)
        }),
    )]
    #[inline]
    pub fn fill(
        &mut self,
        block: LayoutBlock,
        cell: Cell,
    ) where
        Cell: PartialEq,
    {
        let index = usize::from(block);
        let Some(&start) = self.starts.get(index)
        else {
            return;
        };
        let end = start.saturating_add(usize::from(self.block_cells(block)));
        let shared = self.shared.len();
        if let Some(own) = start.checked_sub(shared) {
            if let Some(cells) = self.own.get_mut(own .. end.saturating_sub(shared)) {
                cells.fill(cell);
            }
            return;
        }
        for offset in 0 .. end.saturating_sub(start) {
            if let Some(held) = self.get_mut(NodeIndex::at(block, BlockOffset::from(offset))) {
                held.clone_from(&cell);
            }
        }
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
                if let Some(held) = self
                    .flat(at)
                    .and_then(|flat| cells.get_mut(usize::from(flat)))
                {
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
    use alloc::vec::Vec;

    use gandr_surface_syntax::BlockOffset;
    use gandr_surface_syntax::LayoutBlock;
    use gandr_surface_syntax::NodeCount;
    use gandr_surface_syntax::NodeIndex;

    use super::NodeTable;

    /// #776: a lowering resumed after its closure shares the closure's cells
    /// with the suspended lowering rather than copying them, so a cell one of
    /// them writes at a shared node is its own: the other still reads the
    /// shared cell. Sharing keeps every cell where it was, and widening adds
    /// filled blocks after them.
    #[test]
    fn a_write_to_a_shared_cell_is_the_writer_s_own_776()
    {
        let cells =
            |table: &NodeTable<char>| table.iter().map(|(_, &cell)| cell).collect::<String>();
        let at = |block: usize, offset: usize| {
            NodeIndex::at(LayoutBlock::from(block), BlockOffset::from(offset))
        };
        let blocks = |lengths: &[usize]| {
            lengths
                .iter()
                .copied()
                .map(NodeCount::from)
                .collect::<Vec<_>>()
        };
        let mut suspended = NodeTable::filled(blocks(&[3, 1]), '-');
        *suspended.get_mut(at(0, 1)).expect("node 0.1") = 'b';
        suspended.share();
        assert_eq!(suspended.count(), NodeCount::from(4_usize));
        assert_eq!(suspended.blocks(), LayoutBlock::from(2_usize));
        assert_eq!("-b--", cells(&suspended));

        let mut resumed = suspended.clone();
        assert!(Arc::ptr_eq(&resumed.shared, &suspended.shared));
        resumed.widen(blocks(&[3, 1, 2]), '-');
        assert_eq!(resumed.blocks(), LayoutBlock::from(3_usize));
        *resumed.get_mut(at(0, 0)).expect("node 0.0") = 'a';
        *resumed.get_mut(at(2, 1)).expect("node 2.1") = 'e';
        *resumed.get_mut(at(0, 1)).expect("node 0.1") = '-';

        assert_eq!("a----e", cells(&resumed));
        assert_eq!(resumed.get(at(0, 0)), Some(&'a'));
        assert_eq!(resumed.get(at(1, 1)), None, "an offset past its block");
        assert_eq!(resumed.get(at(2, 2)), None, "an offset past the last block");
        assert_eq!(resumed.get(at(3, 0)), None, "a block past the last");
        assert!(
            Arc::ptr_eq(&resumed.shared, &suspended.shared),
            "the writes leave the shared cells shared"
        );
        assert_eq!(
            "-b--",
            cells(&suspended),
            "and unseen by the suspended table"
        );
        assert_eq!(suspended.get(at(2, 0)), None);

        resumed.share();
        assert_eq!("a----e", cells(&resumed), "sharing keeps every cell");
        assert_eq!("-b--", cells(&suspended), "and still unseen");
    }

    /// Filling a block writes every cell of it and none beside it, whether
    /// the block's cells are shared or the table's own; a shared block filled
    /// stays unseen by the table it was shared with.
    #[test]
    fn filling_a_block_writes_its_cells_alone()
    {
        let cells =
            |table: &NodeTable<char>| table.iter().map(|(_, &cell)| cell).collect::<String>();
        let lengths = [2_usize, 3, 1].map(NodeCount::from);
        let mut suspended = NodeTable::filled(lengths, '-');
        suspended.share();
        let mut resumed = suspended.clone();
        resumed.widen(lengths.into_iter().chain([NodeCount::from(2_usize)]), '-');

        resumed.fill(LayoutBlock::from(1_usize), 's');
        resumed.fill(LayoutBlock::from(3_usize), 'o');
        resumed.fill(LayoutBlock::from(4_usize), 'x');
        assert_eq!("--sss-oo", cells(&resumed));
        assert_eq!("------", cells(&suspended));
    }
}
