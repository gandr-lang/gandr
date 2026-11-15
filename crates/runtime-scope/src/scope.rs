//! The scope: the handle through which the tasks of one run request the
//! kernel's operations.

use ::core::cell::RefCell;
use ::core::marker::PhantomData;

use crate::adapter::Adapter;
use crate::adapter::Native;
use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::op::Op;
use crate::op::Ticket;
use crate::runtime::reap;
use crate::submission::Hold;
use crate::submission::Key;
use crate::submission::Table;

/// The scope of one run. `'env` is the lifetime of the captures of the
/// scope's future, and `'tsk` the lifetime of the scope's tasks, which
/// borrow the scope and the memory that `'env` lends them.
pub struct Scope<'tsk, 'env: 'tsk, A = Native>
where
    A: Adapter,
{
    /// The kernel's adapter.
    adapter: &'tsk RefCell<A>,
    /// The table of the operations in flight.
    table: &'tsk Table,
    /// The brand of the captures.
    phd_env: PhantomData<&'env mut &'env ()>,
    /// The brand of the tasks.
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk, 'env: 'tsk, A> Scope<'tsk, 'env, A>
where
    A: Adapter,
{
    /// The scope of a run on `adapter` with the table `table`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) const fn new(
        adapter: &'tsk RefCell<A>,
        table: &'tsk Table,
    ) -> Self
    {
        Self {
            adapter,
            table,
            phd_tsk: PhantomData,
            phd_env: PhantomData,
        }
    }

    /// A free slot of the table. When every slot is taken and the kernel
    /// holds some of their operations, the caller waits for a drain: the
    /// kernel completes at least one, and its slot may come free.
    ///
    /// # Specification
    ///
    /// - provides: the key of a slot that the call took.
    /// - fails: `Full` when every slot is taken and the kernel holds none of
    ///   their operations, and the error of a drain.
    /// - panics: none.
    /// - executable: none — the slots' states are cells that no predicate of
    ///   the call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a request past the table's depth waits for a drain,
    ///   and gives `Full` when the drain frees no slot.
    /// - witness: `runtime::test::run::full`
    fn slot(&self) -> Result<Key, RuntimeError>
    {
        loop {
            if let Some(key) = self.table.take() {
                return Ok(key);
            }
            if self.table.hold() == Hold::Drained {
                return Err(RuntimeError::Full);
            }
            reap(self.adapter, self.table)?;
        }
    }

    /// Hands `op` to the adapter in a free slot, and gives the completion of
    /// the operation. The run loop starts it, when the adapter does not.
    ///
    /// # Specification
    ///
    /// - requires: each memory that `op` lends outlives `'tsk`.
    /// - ensures: the operation's completion names its slot.
    /// - provides: the completion of the operation, which reads its slot.
    /// - fails: the completion gives `Full` when no slot comes free, the error
    ///   of a drain, and the adapter's refusal of the operation, with
    ///   `Unsupported` for a member that its kernel cannot perform.
    /// - panics: none.
    /// - executable: none — the operation is the kernel's, and the call holds
    ///   nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a thousand no-ops each complete through their slots,
    ///   and a request past the table's depth gives `Full`.
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    /// - witness: `runtime::test::run::full`
    #[inline]
    pub fn request(
        &'tsk self,
        op: Op<'tsk>,
    ) -> Completion<'tsk>
    {
        let key = match self.slot() {
            Ok(key) => key,
            Err(error) => return Completion::refused(self.table, error),
        };
        let submitted = self.adapter.borrow_mut().submit(Ticket(key), op);
        if let Err(error) = submitted {
            self.table.give_back(key);
            return Completion::refused(self.table, error);
        }
        Completion::new(self.table, key)
    }
}
