#![allow(dead_code, reason = "WIP")]
#![allow(unused, reason = "WIP")]
//
#![allow(clippy::missing_docs_in_private_items, reason = "WIP")]
#![allow(clippy::missing_const_for_fn, reason = "WIP")]
#![allow(clippy::missing_errors_doc, reason = "WIP")]
// FIXME:
#![allow(clippy::unused_async, reason = "WIP")]
#![allow(clippy::use_debug, reason = "WIP")]
#![allow(clippy::todo, reason = "WIP")]
#![allow(clippy::print_stdout, reason = "WIP")]

extern crate alloc;

mod buf;
mod completion;
pub mod io;
pub mod net;
mod runtime;
mod scope;
mod submission;

pub use crate::runtime::Runtime;

#[cfg(test)]
pub(crate) mod test
{
    #![allow(clippy::as_conversions, reason = "cfg(test)")]
    #![allow(clippy::cast_possible_truncation, reason = "cfg(test)")]
    #![allow(clippy::print_stdout, reason = "cfg(test)")]
    #![allow(clippy::unwrap_used, reason = "cfg(test)")]

    pub mod harness
    {
        pub mod io
        {
            pub mod socket
            {
                pub use crate::io::socket::test::harness::*;
            }
        }
        pub mod runtime
        {
            pub use crate::runtime::test::harness::*;
        }
    }
}
