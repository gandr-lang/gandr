//! The result of a call of the base.

/// The result of a call of the base: a value, or the error number that the
/// kernel answers.
pub type Result<T> = ::core::result::Result<T, crate::base::sys::linux::errno::Errno>;
