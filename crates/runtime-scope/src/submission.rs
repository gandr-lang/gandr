use ::alloc::boxed::Box;
use ::core::cell::Cell;

use crate::completion::Cqe;

/// The state of one slot of the table.
#[derive(Clone, Copy)]
enum Slot
{
    /// No operation holds the slot.
    Free,
    /// The kernel holds the slot's operation, and its completion waits for it.
    Pending,
    /// The kernel holds the slot's operation, and its completion is dropped.
    Abandoned,
    /// The kernel completed the slot's operation, and its completion has not
    /// read it yet.
    Done(Cqe),
}

/// The table of the operations in flight: one slot for each entry of the
/// ring, made at the start. A key is the index of a slot, and the entry's
/// user data carries it.
pub struct Table
{
    slots: Box<[Cell<Slot>]>,
    free: Box<[Cell<usize>]>,
    free_len: Cell<usize>,
    held: Cell<usize>,
}

impl Table
{
    pub fn new(depth: usize) -> Self
    {
        let slots = ::core::iter::repeat_with(|| Cell::new(Slot::Free))
            .take(depth)
            .collect();
        let free = (0 .. depth).rev().map(Cell::new).collect();
        Self {
            slots,
            free,
            free_len: Cell::new(depth),
            held: Cell::new(0),
        }
    }

    /// The number of operations that the kernel holds.
    pub const fn held(&self) -> usize
    {
        self.held.get()
    }

    /// Takes a free slot for an operation, or gives nothing when every slot
    /// is taken.
    pub fn take(&self) -> Option<usize>
    {
        let len = self.free_len.get().checked_sub(1)?;
        let key = self.free.get(len)?.get();
        self.free_len.set(len);
        self.slots.get(key)?.set(Slot::Pending);
        self.held.set(self.held.get().saturating_add(1));
        Some(key)
    }

    /// Gives back a slot that `take` gave for an entry that the ring never
    /// took.
    pub fn give_back(
        &self,
        key: usize,
    )
    {
        self.held.set(self.held.get().saturating_sub(1));
        self.release(key);
    }

    /// Records the kernel's completion of the operation in slot `key`, and
    /// gives whether the slot held an operation of the kernel.
    pub fn complete(
        &self,
        key: usize,
        cqe: Cqe,
    ) -> bool
    {
        let Some(slot) = self.slots.get(key)
        else {
            return false;
        };
        match slot.get() {
            Slot::Pending => slot.set(Slot::Done(cqe)),
            Slot::Abandoned => self.release(key),
            Slot::Free | Slot::Done(_) => return false,
        }
        self.held.set(self.held.get().saturating_sub(1));
        true
    }

    /// Reads the completion of the operation in slot `key` and frees the
    /// slot, or gives nothing while the kernel holds the operation.
    pub fn read(
        &self,
        key: usize,
    ) -> Option<Cqe>
    {
        let Slot::Done(cqe) = self.slots.get(key)?.get()
        else {
            return None;
        };
        self.release(key);
        Some(cqe)
    }

    /// Records that the completion of slot `key` is dropped: the slot stays
    /// taken until the kernel completes the operation.
    pub fn abandon(
        &self,
        key: usize,
    )
    {
        let Some(slot) = self.slots.get(key)
        else {
            return;
        };
        match slot.get() {
            Slot::Pending => slot.set(Slot::Abandoned),
            Slot::Done(_) => self.release(key),
            Slot::Free | Slot::Abandoned => {},
        }
    }

    /// Frees slot `key`.
    fn release(
        &self,
        key: usize,
    )
    {
        let len = self.free_len.get();
        if let (Some(slot), Some(free)) = (self.slots.get(key), self.free.get(len)) {
            slot.set(Slot::Free);
            free.set(key);
            self.free_len.set(len.saturating_add(1));
        }
    }
}
