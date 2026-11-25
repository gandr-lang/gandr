//! The runtime's one error type.

use ::core::fmt;
use ::rustix::io::Errno;

/// The runtime's refusal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum RuntimeError
{
    /// The kernel refused an operation or a system call with this error.
    Kernel(Errno),
    /// The ring's crate refused a call with an error of no number.
    Ring(::std::io::ErrorKind),
    /// The table held no free slot for a request, and no drain freed one.
    Full,
    /// A completion was polled again after it gave its result.
    Read,
    /// The kernel's count of bytes passed the length of the buffer that the
    /// operation lent it.
    Overrun,
    /// The kernel refused the cancel of the operation in slot `data` at a
    /// scope's end, with this error.
    Cancel
    {
        /// The slot of the operation that the cancel names.
        data: u64,
        /// The kernel's error.
        errno: Errno,
    },
    /// A completion's user data named no slot of the table.
    Unknown(u64),
    /// An earlier run of the runtime failed, so the kernel can hold that
    /// run's operations. The runtime takes no further run.
    Spent,
}

impl From<::std::io::Error> for RuntimeError
{
    /// The kernel's error that `error` carries, or the kind of a refusal of
    /// the ring's crate with no number.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(error: ::std::io::Error) -> Self
    {
        Errno::from_io_error(&error).map_or_else(|| Self::Ring(error.kind()), Self::Kernel)
    }
}

impl fmt::Display for RuntimeError
{
    /// The refusal, in words.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Kernel(errno) => write!(f, "the kernel refused the operation: {errno}"),
            Self::Ring(kind) => write!(f, "the ring refused the call: {kind}"),
            Self::Full => f.write_str("submission queue full"),
            Self::Read => f.write_str("completion polled after its result"),
            Self::Overrun => f.write_str("the kernel's count passed the buffer"),
            Self::Cancel { data, errno } => {
                write!(
                    f,
                    "the kernel refused the cancel of the operation in slot {data}: {errno}"
                )
            },
            Self::Unknown(data) => write!(f, "task lookup failed: {data}"),
            Self::Spent => f.write_str("an earlier run failed, and the runtime is spent"),
        }
    }
}

impl core::error::Error for RuntimeError
{
}
