//! The scoped runtime: one thread drives the futures of a scope over the
//! kernel's ring, and the scope's end drains every operation of the scope.
//!
//! A `Runtime` owns the ring. `Runtime::run` gives the scope's future a
//! `Scope`, through which each task requests the kernel's operations. The
//! memory of an operation is a borrow of the scope's life, so the kernel
//! writes only memory that the scope holds.

// The runtime stands on the Linux kernel's ring: on another system the crate
// compiles empty.
#![cfg(target_os = "linux")]

extern crate alloc;

mod completion;
mod error;
/// The operations of the scope on the kernel's files.
pub mod io
{
    pub mod buf;
    pub mod socket;
}
mod runtime;
mod scope;
mod submission;

pub use crate::error::RuntimeError;
pub use crate::runtime::Runtime;
pub use crate::scope::Scope;
pub use crate::submission::Depth;

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
