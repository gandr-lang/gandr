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
    /// A completion's user data named no slot of the table.
    Unknown(u64),
}

impl RuntimeError
{
    /// The refusal of a completion whose result is the negated error number
    /// `res`.
    pub(crate) fn completion(res: i32) -> Self
    {
        Self::Kernel(Errno::from_raw_os_error(res.saturating_neg()))
    }
}

impl From<::std::io::Error> for RuntimeError
{
    #[inline]
    fn from(error: ::std::io::Error) -> Self
    {
        Errno::from_io_error(&error).map_or_else(|| Self::Ring(error.kind()), Self::Kernel)
    }
}

impl fmt::Display for RuntimeError
{
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
            Self::Unknown(data) => write!(f, "task lookup failed: {data}"),
        }
    }
}

impl core::error::Error for RuntimeError
{
}
