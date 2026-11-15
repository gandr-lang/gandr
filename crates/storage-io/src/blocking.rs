//! The blocking form: the worker's own thread runs each order in turn by
//! positioned calls of the standard library, when the `Io` submits it, and
//! keeps each completion in the form's queue. A chain breaks as the ring's
//! does: an order that fails, or moves fewer bytes than it asks, cancels
//! each order linked after it.
//!
//! The form owns no thread. The pool's workers are its bounded blocking
//! threads, one for each worker, as each worker owns one ring.

use alloc::collections::VecDeque;
use core::alloc::Allocator;

use crate::io::Chain;
use crate::io::Done;
use crate::io::Fate;
use crate::io::Operation;
use crate::io::Order;
use crate::ring::Count;
use crate::ring::Moved;
use crate::sys::Errno;

/// Whether the order before broke its chain.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Link
{
    /// The next order runs.
    Whole,
    /// The next order completes cancelled.
    Broken,
}

/// The blocking form: the completions that its orders gave.
#[repr(transparent)]
pub struct Blocking<A>
where
    A: Allocator,
{
    /// The completions in the order of their submissions, at most `depth`.
    done: VecDeque<Done<A>>,
}

impl<A> Blocking<A>
where
    A: Allocator,
{
    /// The blocking form of `depth` orders in flight.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(depth: Count) -> Self
    {
        Self {
            done: VecDeque::with_capacity(usize::try_from(u32::from(depth)).unwrap_or(usize::MAX)),
        }
    }

    /// Run each staged order in turn, and keep its completion.
    ///
    /// # Specification
    /// - ensures: `staged` is empty, and the form holds one completion for each
    ///   order it held, in their order.
    /// - panics: none.
    /// - executable: none — the files are the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form completes a linked write, sync and
    ///   read in order, and a failed write cancels the sync linked to it.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    /// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
    #[inline]
    pub fn flush(
        &mut self,
        staged: &mut Vec<Order<A>>,
    )
    {
        let mut link = Link::Whole;
        for order in staged.drain(..) {
            self.done.push_back(run(order, &mut link));
        }
    }

    /// The next completion that stands, if one does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn take(&mut self) -> Option<Done<A>>
    {
        self.done.pop_front()
    }
}

/// Run `order` by one positioned call, after the chain of the order before.
///
/// # Specification
/// - ensures: the order's completion. A cancelled order, or one after a broken
///   chain, completes with [`Errno::CANCELLED`] and runs nothing. A linked
///   order that fails or moves fewer bytes than it asks breaks the chain.
/// - panics: none.
/// - executable: none — the file is the kernel's.
///
/// # Adequacy
/// - hypothesis: L3 — a write that fails cancels the sync linked to it, as the
///   ring does.
/// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
fn run<A>(
    mut order: Order<A>,
    link: &mut Link,
) -> Done<A>
where
    A: Allocator,
{
    let at = order.landing();
    let asked = order.kept(order.operation.asked());
    let outcome = if *link == Link::Broken || order.fate == Fate::Cancelled {
        Err(Errno::CANCELLED)
    }
    else {
        match order.operation {
            Operation::Read {
                ref handle,
                ref mut buffer,
            } => buffer.read_from(handle.file(), at),
            Operation::Write {
                ref handle,
                ref buffer,
            } => buffer.write_into(handle.file(), at, asked),
            Operation::Sync { ref handle } => handle
                .file()
                .sync_data()
                .map(|()| Moved::from(0))
                .map_err(Errno::from),
            Operation::Cancel { .. } => Err(Errno::INVALID),
        }
    };
    let whole = outcome.is_ok_and(|moved| moved >= asked);
    *link = if order.chain == Chain::Linked && !whole {
        Link::Broken
    }
    else {
        Link::Whole
    };
    order.done(outcome)
}
