//! The one operation set of the scope: each operation that an adapter
//! performs, the same set for each kernel.
//!
//! The set is cut to the ring's whole ability. An adapter whose kernel
//! cannot perform a member refuses it by name with
//! [`RuntimeError::Unsupported`](crate::RuntimeError::Unsupported), so a hole
//! shows and is never silent. Each memory that an operation lends the kernel
//! is a borrow of the scope's life `'tsk`, which the scope's end drains
//! before the borrow ends.

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::io::buf::Buf;
use crate::submission::Key;

/// A descriptor that an operation names: a file, a pipe or a socket of the
/// kernel, which the operation borrows until its completion.
#[cfg(unix)]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Descriptor(::std::os::fd::RawFd);

/// A descriptor that an operation names: a file, a pipe or a socket of the
/// kernel, which the operation borrows until its completion.
#[cfg(windows)]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Descriptor(::std::os::windows::io::RawHandle);

#[cfg(unix)]
impl<T> From<&T> for Descriptor
where
    T: ::std::os::fd::AsRawFd,
{
    /// The descriptor of `file`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(file: &T) -> Self
    {
        Self(file.as_raw_fd())
    }
}

#[cfg(windows)]
impl<T> From<&T> for Descriptor
where
    T: ::std::os::windows::io::AsRawHandle,
{
    /// The handle of `file`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(file: &T) -> Self
    {
        Self(file.as_raw_handle())
    }
}

#[cfg(unix)]
impl From<Descriptor> for ::std::os::fd::RawFd
{
    /// The descriptor's number.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(descriptor: Descriptor) -> Self
    {
        descriptor.0
    }
}

#[cfg(windows)]
impl From<Descriptor> for ::std::os::windows::io::RawHandle
{
    /// The handle.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(descriptor: Descriptor) -> Self
    {
        descriptor.0
    }
}

/// Bytes that an operation lends the kernel for the scope's life: their
/// address and their length. The kernel writes them for a read and reads
/// them for a write.
#[derive(Clone, Copy, Debug)]
pub struct Lent<'tsk>
{
    /// The first byte.
    ptr: NonNull<u8>,
    /// The count of bytes.
    len: usize,
    /// The borrow of the bytes for the scope's life.
    phd: PhantomData<&'tsk mut [u8]>,
}

impl<'tsk> Lent<'tsk>
{
    /// The bytes of `buf`, lent until the scope ends. The caller keeps `buf`
    /// and reads it only after the operation's completion.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub(crate) fn of(buf: &mut Buf<'tsk>) -> Self
    {
        let len = buf.len();
        Self {
            ptr: NonNull::from(&mut **buf).cast(),
            len,
            phd: PhantomData,
        }
    }

    /// The first byte's address.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ptr(self) -> NonNull<u8>
    {
        self.ptr
    }

    /// The count of bytes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn len(self) -> Length
    {
        Length(self.len)
    }
}

/// A count of bytes that an operation lends the kernel.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Length(usize);

impl From<Length> for usize
{
    /// The count.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(length: Length) -> Self
    {
        length.0
    }
}

/// The span of a timer: whole seconds and the nanoseconds past them, as the
/// kernels read a time. The caller lends it for the scope's life, since a
/// ring reads it only when it takes the timer's entry.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Timeout
{
    /// The whole seconds.
    secs: i64,
    /// The nanoseconds past them, below one second.
    nanos: i64,
}

impl From<::core::time::Duration> for Timeout
{
    /// The span of `duration`, its seconds saturated at the largest span a
    /// kernel reads.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(duration: ::core::time::Duration) -> Self
    {
        Self {
            secs: i64::try_from(duration.as_secs()).unwrap_or(i64::MAX),
            nanos: i64::from(duration.subsec_nanos()),
        }
    }
}

impl From<Timeout> for ::core::time::Duration
{
    /// The span as a duration.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(timeout: Timeout) -> Self
    {
        let secs = u64::try_from(timeout.secs).unwrap_or(0);
        let nanos = u32::try_from(timeout.nanos).unwrap_or(0);
        Self::new(secs, nanos)
    }
}

/// The ticket of an operation in flight: the slot that a cancel names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Ticket(pub(crate) Key);

/// One member of the operation set, by name: what a refusal names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Member
{
    /// An operation that does nothing.
    Nop,
    /// A read of a descriptor into lent bytes.
    Read,
    /// A write of lent bytes to a descriptor.
    Write,
    /// An accept of a connection on a listening socket.
    Accept,
    /// A timer of a span.
    Timer,
    /// A cancel of an operation in flight.
    Cancel,
    /// A write linked to the sync of its file: one completion for the pair.
    WriteSync,
    /// The creation of a socket.
    Socket,
    /// A bind of a socket to an address.
    Bind,
    /// A listen on a socket.
    Listen,
    /// A receive of a socket's bytes.
    Recv,
}

/// The one operation set: each operation that the scope requests of its
/// adapter. Each lent memory is a borrow of the scope's life.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Op<'tsk>
{
    /// An operation that does nothing, and completes.
    Nop,
    /// A read of at most the lent bytes from the descriptor, at its offset.
    Read
    {
        /// The descriptor read.
        fd: Descriptor,
        /// The bytes that the kernel writes.
        into: Lent<'tsk>,
    },
    /// A write of the lent bytes to the descriptor, at its offset.
    Write
    {
        /// The descriptor written.
        fd: Descriptor,
        /// The bytes that the kernel reads.
        from: Lent<'tsk>,
    },
    /// An accept of a connection on a listening socket, whose peer's address
    /// the kernel writes into lent storage.
    Accept
    {
        /// The listening socket.
        fd: Descriptor,
        /// The peer's storage.
        peer: NonNull<::socket2::SockAddrStorage>,
        /// The peer's length: the storage's size before, the address's after.
        len: NonNull<::socket2::socklen_t>,
        /// The borrow of the storage for the scope's life.
        phd: PhantomData<&'tsk mut ::socket2::SockAddrStorage>,
    },
    /// A timer that completes once its span passes.
    Timer
    {
        /// The span, lent for the scope's life.
        after: &'tsk Timeout,
    },
    /// A cancel of the operation that the ticket names. The cancel completes,
    /// and so does the operation, with the kernel's cancelled refusal when
    /// the cancel caught it.
    Cancel
    {
        /// The operation's ticket.
        target: Ticket,
    },
    /// A write of the lent bytes linked to the sync of the descriptor's file:
    /// the sync starts after the write completes, and the pair completes
    /// once, with the write's count or the first refusal.
    WriteSync
    {
        /// The file written and synced.
        fd: Descriptor,
        /// The bytes that the kernel reads.
        from: Lent<'tsk>,
    },
    /// The creation of a socket.
    Socket
    {
        /// The socket's domain.
        domain: ::socket2::Domain,
        /// The socket's type.
        ty: ::socket2::Type,
        /// The socket's protocol, or the domain's default.
        protocol: Option<::socket2::Protocol>,
    },
    /// A bind of a socket to a lent address.
    Bind
    {
        /// The socket bound.
        fd: Descriptor,
        /// The address, lent for the scope's life.
        addr: &'tsk ::socket2::SockAddr,
    },
    /// A listen on a socket with a queue of connections.
    Listen
    {
        /// The socket.
        fd: Descriptor,
        /// The length of the queue of connections.
        backlog: crate::io::socket::Backlog,
    },
    /// A receive of at most the lent bytes from a socket.
    Recv
    {
        /// The socket.
        fd: Descriptor,
        /// The bytes that the kernel writes.
        into: Lent<'tsk>,
    },
}

impl Op<'_>
{
    /// The member of the set that the operation is.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn member(&self) -> Member
    {
        match *self {
            Self::Nop => Member::Nop,
            Self::Read { .. } => Member::Read,
            Self::Write { .. } => Member::Write,
            Self::Accept { .. } => Member::Accept,
            Self::Timer { .. } => Member::Timer,
            Self::Cancel { .. } => Member::Cancel,
            Self::WriteSync { .. } => Member::WriteSync,
            Self::Socket { .. } => Member::Socket,
            Self::Bind { .. } => Member::Bind,
            Self::Listen { .. } => Member::Listen,
            Self::Recv { .. } => Member::Recv,
        }
    }
}
