//! The adapter: the one seam between the scope and a kernel. The runtime
//! owns the slot table, the lent memory and the scope's end; an adapter
//! performs the operations of [`Op`](crate::Op) on its kernel and records
//! each completion in its slot.
//!
//! Each target takes one adapter, [`Native`], at compile time, so a program
//! names none and no table of methods runs: the runtime is generic in its
//! adapter and monomorphised for the target. A test names an adapter.

#[cfg(target_os = "macos")]
pub mod kqueue;
#[cfg(target_os = "linux")]
pub mod uring;

use crate::error::RuntimeError;
use crate::op::Op;
use crate::op::Ticket;
use crate::submission::Depth;
use crate::submission::Table;

/// A kernel's adapter: it opens the kernel's queue, performs each operation
/// of the set on it, cancels one in flight, and records each completion in
/// the runtime's table.
///
/// # Specification
///
/// - provides: one completion in the operation's slot for each operation that
///   `submit` takes, and for each cancel's target.
/// - declaration-only: each adapter states its own kernel's path.
pub trait Adapter: Sized
{
    /// The adapter of a new queue of the kernel, with room for `depth`
    /// operations in flight.
    ///
    /// # Specification
    ///
    /// - provides: an adapter with room for `depth` operations.
    /// - fails: the kernel's refusal of the queue.
    /// - declaration-only: the queue is each kernel's.
    ///
    /// # Errors
    ///
    /// The kernel's refusal.
    fn open(depth: Depth) -> Result<Self, RuntimeError>;

    /// Starts `op` in the slot that `ticket` names. The kernel may start it
    /// at once or at the next `wait`.
    ///
    /// # Specification
    ///
    /// - requires: the slot is pending, and each memory that `op` lends
    ///   outlives the operation's completion.
    /// - ensures: on success, a later `wait` records the operation's completion
    ///   in its slot.
    /// - fails: `Unsupported` with the member for a member that the kernel
    ///   cannot perform, `Full` when the queue has no room, and the kernel's
    ///   refusal.
    /// - declaration-only: the path is each kernel's.
    ///
    /// # Errors
    ///
    /// As `fails` states.
    fn submit(
        &mut self,
        ticket: Ticket,
        op: Op<'_>,
    ) -> Result<(), RuntimeError>;

    /// Cancels the operation in flight in the slot that `ticket` names, at the
    /// scope's end. The operation's own completion follows, as the slot's.
    ///
    /// # Specification
    ///
    /// - requires: the slot's operation is in flight.
    /// - ensures: the operation completes at a later `wait`.
    /// - fails: `Full` when the queue has no room after a flush, and the
    ///   kernel's refusal.
    /// - declaration-only: the path is each kernel's.
    ///
    /// # Errors
    ///
    /// As `fails` states.
    fn cancel(
        &mut self,
        ticket: Ticket,
    ) -> Result<(), RuntimeError>;

    /// Starts each operation that `submit` took, waits until at least one
    /// completes, and records each completion that is ready in its slot of
    /// `table`.
    ///
    /// # Specification
    ///
    /// - ensures: each ready completion is in its slot.
    /// - fails: the kernel's refusal of the wait, `Cancel` with the slot when a
    ///   cancel fails, and `Unknown` when a completion names no slot.
    /// - declaration-only: the path is each kernel's.
    ///
    /// # Errors
    ///
    /// As `fails` states.
    fn wait(
        &mut self,
        table: &Table,
    ) -> Result<(), RuntimeError>;
}

/// The socket that `fd` names, borrowed while an adapter performs or
/// prepares its operation.
///
/// # Safety
///
/// - unsafe invariants: `fd` is an open descriptor that the operation borrows
///   until its completion.
///
/// # Specification
///
/// trivial.
#[cfg(unix)]
unsafe fn socket_of(fd: crate::op::Descriptor) -> ::std::mem::ManuallyDrop<::socket2::Socket>
{
    // SAFETY: the caller's invariant; the socket is never dropped, so the
    // descriptor stays its owner's.
    let socket = unsafe { <::socket2::Socket as ::std::os::fd::FromRawFd>::from_raw_fd(fd.into()) };
    ::std::mem::ManuallyDrop::new(socket)
}

/// The adapter of the target: the kernel's ring on Linux.
#[cfg(target_os = "linux")]
pub type Native = uring::Uring;

/// The adapter of the target: the kernel's queue of events on macOS.
#[cfg(target_os = "macos")]
pub type Native = kqueue::Kqueue;

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
::core::compile_error!(
    "gandr-runtime-scope has no adapter for this target: the targets are Linux (io_uring), macOS (kqueue) and Windows (IOCP and IoRing)"
);
