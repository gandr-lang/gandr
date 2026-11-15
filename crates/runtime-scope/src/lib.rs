//! The scoped runtime: one thread drives the futures of a scope over the
//! kernel's queue, and the scope's end drains every operation of the scope.
//!
//! A `Runtime` owns the kernel's adapter. `Runtime::run` gives the scope's
//! future a `Scope`, through which each task requests the operations of the
//! one set, [`Op`]. The memory of an operation is a borrow of the scope's
//! life, so the kernel writes only memory that the scope holds.

// Each target takes its kernel's adapter. A target with none is refused by
// name at compile time (`adapter`).

extern crate alloc;

mod adapter;
mod completion;
mod error;
/// The operations of the scope on the kernel's files.
pub mod io
{
    pub mod buf;
    pub mod fd;
    pub mod socket;
}
mod op;
mod runtime;
mod scope;
mod submission;

pub use crate::adapter::Adapter;
pub use crate::adapter::Native;
#[cfg(target_os = "macos")]
pub use crate::adapter::kqueue::Kqueue;
#[cfg(target_os = "linux")]
pub use crate::adapter::uring::Uring;
pub use crate::completion::Completion;
pub use crate::completion::Count;
pub use crate::error::RuntimeError;
pub use crate::op::Descriptor;
pub use crate::op::Length;
pub use crate::op::Lent;
pub use crate::op::Member;
pub use crate::op::Op;
pub use crate::op::Ticket;
pub use crate::op::Timeout;
pub use crate::runtime::Runtime;
pub use crate::scope::Scope;
pub use crate::submission::Depth;
pub use crate::submission::Table;

/// The harnesses of the crate's tests, one for each area.
#[cfg(test)]
pub(crate) mod test
{
    /// The harnesses of the tests, by the module that each tests.
    pub mod harness
    {
        /// The harnesses of the operations' tests.
        pub mod io
        {
            /// The harnesses of the socket's tests.
            pub mod socket
            {
                pub use crate::io::socket::test::harness::*;
            }
        }
        /// The harnesses of the runtime's tests.
        pub mod runtime
        {
            pub use crate::runtime::test::harness::*;
        }
    }
}
