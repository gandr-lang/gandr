//! The table of the operations in flight: one slot for each entry of the
//! ring, made once at the start of a run.

use ::alloc::boxed::Box;
use ::core::cell::Cell;

use crate::completion::Cqe;

/// The key of a slot of the table: its index. The user data of the slot's
/// entry carries it, so the kernel's completion names its slot.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Key(usize);

impl From<Key> for usize
{
    /// The slot's index.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(key: Key) -> Self
    {
        key.0
    }
}

impl TryFrom<Key> for u64
{
    type Error = ::core::num::TryFromIntError;

    /// The user data of the slot's entry.
    ///
    /// # Specification
    ///
    /// - provides: the slot's index as the entry's user data.
    /// - fails: on a target whose index is wider than 64 bits, past `u64::MAX`.
    /// - panics: none.
    /// - executable: none — the conversion is the standard library's.
    #[inline]
    fn try_from(key: Key) -> Result<Self, Self::Error>
    {
        Self::try_from(key.0)
    }
}

impl TryFrom<u64> for Key
{
    type Error = ::core::num::TryFromIntError;

    /// The key that a completion's user data names.
    ///
    /// # Specification
    ///
    /// - provides: the user data as a slot's index.
    /// - fails: on a target whose index is narrower than the user data.
    /// - panics: none.
    /// - executable: none — the conversion is the standard library's.
    #[inline]
    fn try_from(data: u64) -> Result<Self, Self::Error>
    {
        usize::try_from(data).map(Self)
    }
}

/// The count of a table's slots: the depth of the ring.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Depth(usize);

impl From<u16> for Depth
{
    /// The depth of a ring of `entries` entries.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(entries: u16) -> Self
    {
        Self(usize::from(entries))
    }
}

/// Whether the kernel holds an operation of the table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Hold
{
    /// The kernel holds no operation of the table.
    Drained,
    /// The kernel holds at least one operation of the table.
    Held,
}

/// Whether a completion's key named a slot whose operation the kernel held.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Lookup
{
    /// The slot held the operation, and records its completion.
    Found,
    /// No slot of the key held an operation of the kernel.
    Missing,
}

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
/// ring, made at the start. Each slot is free, pending, abandoned or done,
/// and a stack holds the keys of the free slots.
pub struct Table
{
    /// The slots, one for each entry of the ring.
    slots: Box<[Cell<Slot>]>,
    /// The keys of the free slots, a stack below `free_len`.
    free: Box<[Cell<Key>]>,
    /// The count of free keys on the stack.
    free_len: Cell<usize>,
    /// The count of slots whose operations the kernel holds.
    held: Cell<usize>,
}

impl Table
{
    /// A table of `depth` free slots.
    ///
    /// # Specification
    ///
    /// trivial.
    ///
    /// # Cost
    ///
    /// - allocation: the slots and the stack of free keys, setup
    pub fn new(depth: Depth) -> Self
    {
        let slots = ::core::iter::repeat_with(|| Cell::new(Slot::Free))
            .take(depth.0)
            .collect();
        let free = (0 .. depth.0)
            .rev()
            .map(|key| Cell::new(Key(key)))
            .collect();
        Self {
            slots,
            free,
            free_len: Cell::new(depth.0),
            held: Cell::new(0),
        }
    }

    /// Whether the kernel holds an operation of the table.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn hold(&self) -> Hold
    {
        if self.held.get() == 0 {
            Hold::Drained
        }
        else {
            Hold::Held
        }
    }

    /// The keys of the slots whose operations the kernel holds.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn in_kernel(&self) -> impl Iterator<Item = Key> + '_
    {
        self.slots
            .iter()
            .enumerate()
            .filter(|&(_key, slot)| matches!(slot.get(), Slot::Pending | Slot::Abandoned))
            .map(|(key, _slot)| Key(key))
    }

    /// Takes a free slot for an operation, or gives nothing when every slot
    /// is taken.
    ///
    /// # Specification
    ///
    /// - ensures: on `Some`, the slot is pending, and the kernel holds one more
    ///   operation of the table.
    /// - provides: the key of a slot that no other operation holds.
    /// - fails: `None` when no slot is free.
    /// - panics: none.
    /// - executable: none — the slots' states are cells that no predicate of
    ///   the call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a run takes every slot, is refused the next, and
    ///   takes a slot again once the held completions drop.
    /// - witness: `runtime::test::run::full`
    pub fn take(&self) -> Option<Key>
    {
        let len = self.free_len.get().checked_sub(1)?;
        let key = self.free.get(len)?.get();
        self.free_len.set(len);
        self.slots.get(key.0)?.set(Slot::Pending);
        self.held.set(self.held.get().saturating_add(1));
        Some(key)
    }

    /// Gives back a slot that `take` gave for an entry that the ring never
    /// took.
    ///
    /// # Specification
    ///
    /// trivial.
    pub fn give_back(
        &self,
        key: Key,
    )
    {
        self.held.set(self.held.get().saturating_sub(1));
        self.release(key);
    }

    /// Records the kernel's completion of the operation in slot `key`.
    ///
    /// # Specification
    ///
    /// - ensures: on `Found`, a pending slot is done with `cqe`, an abandoned
    ///   slot is free, and the kernel holds one operation of the table fewer.
    /// - provides: `Missing` when the slot is free or already done.
    /// - panics: none.
    /// - executable: none — the slots' states are cells that no predicate of
    ///   the call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — an accept that the scope abandons completes into a
    ///   free slot, and a request that its scope awaits reads its completion
    ///   from the slot.
    /// - witness: `io::socket::test::socket::accept_in_flight`
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    pub fn complete(
        &self,
        key: Key,
        cqe: Cqe,
    ) -> Lookup
    {
        let Some(slot) = self.slots.get(key.0)
        else {
            return Lookup::Missing;
        };
        match slot.get() {
            Slot::Pending => slot.set(Slot::Done(cqe)),
            Slot::Abandoned => self.release(key),
            Slot::Free | Slot::Done(_) => return Lookup::Missing,
        }
        self.held.set(self.held.get().saturating_sub(1));
        Lookup::Found
    }

    /// Reads the completion of the operation in slot `key` and frees the
    /// slot, or gives nothing while the kernel holds the operation.
    ///
    /// # Specification
    ///
    /// - ensures: on `Some`, the slot is free.
    /// - provides: the completion that `complete` recorded.
    /// - fails: `None` while the slot is not done.
    /// - panics: none.
    /// - executable: none — the slots' states are cells that no predicate of
    ///   the call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a thousand requests read their completions, and each
    ///   frees its slot for the next.
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    pub fn read(
        &self,
        key: Key,
    ) -> Option<Cqe>
    {
        let Slot::Done(cqe) = self.slots.get(key.0)?.get()
        else {
            return None;
        };
        self.release(key);
        Some(cqe)
    }

    /// Records that the completion of slot `key` is dropped: the slot stays
    /// taken until the kernel completes the operation.
    ///
    /// # Specification
    ///
    /// - ensures: a pending slot is abandoned, and a done slot is free.
    /// - panics: none.
    /// - executable: none — the slots' states are cells that no predicate of
    ///   the call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — an accept and a receive that their scopes drop stay
    ///   in the kernel until the scope's end cancels them, and done slots whose
    ///   completions drop come free.
    /// - witness: `io::socket::test::socket::accept_in_flight`
    /// - witness: `io::socket::test::socket::recv_in_flight`
    /// - witness: `runtime::test::run::full`
    pub fn abandon(
        &self,
        key: Key,
    )
    {
        let Some(slot) = self.slots.get(key.0)
        else {
            return;
        };
        match slot.get() {
            Slot::Pending => slot.set(Slot::Abandoned),
            Slot::Done(_) => self.release(key),
            Slot::Free | Slot::Abandoned => {},
        }
    }

    /// Frees slot `key`, and puts its key on the stack of free keys.
    ///
    /// # Specification
    ///
    /// trivial.
    fn release(
        &self,
        key: Key,
    )
    {
        let len = self.free_len.get();
        if let (Some(slot), Some(free)) = (self.slots.get(key.0), self.free.get(len)) {
            slot.set(Slot::Free);
            free.set(key);
            self.free_len.set(len.saturating_add(1));
        }
    }
}
