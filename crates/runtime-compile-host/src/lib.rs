//! Positive-core program images and the versioned compile-host vocabulary.
//!
//! Enable the compile-host feature for the Rust preparation surface. No foreign
//! host is linked, loaded or executed by this crate.

#![cfg(feature = "compile-host")]

pub mod boundary;
pub mod image;
mod lower;
pub mod render;
mod typed;

pub use lower::Form;
pub use lower::LowerError;
pub use lower::lower_computation;
pub use typed::BridgeError;
pub use typed::TypedVerdict;
pub use typed::check_and_lower;
pub use typed::is_typed;
