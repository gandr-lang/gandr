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
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — each request's key goes into its entry's user data,
    ///   and its completion names the same slot.
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    /// - witness: `runtime::test::run::full`
    /// - witness: `submission::test::table::a_key_round_trips_through_the_user_data`
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
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — each completion's user data names the slot of its
    ///   request.
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    /// - witness: `runtime::test::run::full`
    /// - witness: `submission::test::table::a_key_round_trips_through_the_user_data`
    #[inline]
    fn try_from(data: u64) -> Result<Self, Self::Error>
    {
        usize::try_from(data).map(Self)
    }
}

/// The count of a table's slots: the depth of the ring.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Depth(u16);

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
        Self(entries)
    }
}

impl From<Depth> for u16
{
    /// The count of the ring's entries at `depth`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(depth: Depth) -> Self
    {
        depth.0
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
        let depth = usize::from(depth.0);
        let slots = ::core::iter::repeat_with(|| Cell::new(Slot::Free))
            .take(depth)
            .collect();
        let free = (0 .. depth).rev().map(|key| Cell::new(Key(key))).collect();
        Self {
            slots,
            free,
            free_len: Cell::new(depth),
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
    /// - witness: `submission::test::table::takes_each_slot_then_refuses`
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
    /// - witness: `submission::test::table::a_read_frees_its_slot`
    /// - witness: `submission::test::table::a_completion_of_no_held_slot_is_missing`
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
    /// - witness: `submission::test::table::a_read_frees_its_slot`
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
    /// - witness: `submission::test::table::an_abandoned_slot_frees_at_its_completion`
    /// - witness: `completion::test::completion::a_dropped_completion_leaves_its_slot_to_the_kernel`
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

/// The table's tests. No ring takes part, so Miri runs each one.
#[cfg(test)]
mod test
{
    use super::*;

    /// The states of the table's slots.
    mod table
    {
        use super::*;

        #[test]
        fn takes_each_slot_then_refuses()
        {
            let table = Table::new(Depth::from(2_u16));
            let first = table.take().unwrap();
            let second = table.take().unwrap();
            assert_ne!(first, second);
            assert_eq!(table.take(), None);
            assert_eq!(table.hold(), Hold::Held);
        }

        #[test]
        fn a_read_frees_its_slot()
        {
            let table = Table::new(Depth::from(1_u16));
            let key = table.take().unwrap();
            assert!(table.read(key).is_none());
            assert_eq!(table.complete(key, Cqe::ZERO), Lookup::Found);
            assert_eq!(table.hold(), Hold::Drained);
            assert!(table.read(key).is_some());
            assert_eq!(table.take(), Some(key));
        }

        #[test]
        fn an_abandoned_slot_frees_at_its_completion()
        {
            let table = Table::new(Depth::from(1_u16));
            let key = table.take().unwrap();
            table.abandon(key);
            assert_eq!(table.take(), None);
            assert_eq!(table.hold(), Hold::Held);
            assert_eq!(table.complete(key, Cqe::ZERO), Lookup::Found);
            assert_eq!(table.hold(), Hold::Drained);
            assert_eq!(table.take(), Some(key));
        }

        #[test]
        fn a_completion_of_no_held_slot_is_missing()
        {
            let table = Table::new(Depth::from(1_u16));
            let key = table.take().unwrap();
            table.give_back(key);
            assert_eq!(table.complete(key, Cqe::ZERO), Lookup::Missing);
            assert_eq!(table.complete(Key(7), Cqe::ZERO), Lookup::Missing);
            assert_eq!(table.hold(), Hold::Drained);
        }

        #[test]
        fn the_kernel_s_slots_are_the_pending_and_the_abandoned()
        {
            let table = Table::new(Depth::from(3_u16));
            let pending = table.take().unwrap();
            let abandoned = table.take().unwrap();
            let done = table.take().unwrap();
            table.abandon(abandoned);
            table.complete(done, Cqe::ZERO);
            let held = table.in_kernel().collect::<Vec<_>>();
            assert_eq!(held.len(), 2);
            assert!(held.contains(&pending));
            assert!(held.contains(&abandoned));
        }

        #[test]
        fn a_key_round_trips_through_the_user_data()
        {
            let table = Table::new(Depth::from(4_u16));
            let key = table.take().unwrap();
            let data = u64::try_from(key).unwrap();
            assert_eq!(Key::try_from(data), Ok(key));
        }
    }
}
