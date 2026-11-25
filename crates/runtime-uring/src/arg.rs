//! The arguments of the ring's calls, each a newtype by its role.
//!
//! A preparer takes the kernel's C type inside the newtype, so its signature
//! names what each argument is to the kernel. Each newtype is transparent and
//! has the layout of its C type.

/// A file that an entry names: a descriptor of the process, or a slot of the
/// ring's file table when the entry carries the fixed-file flag.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fd(pub ::core::ffi::c_int);

/// A set of flags, or a mask, in the C type `B` that the kernel reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Flags<B>(pub B);

/// A length in bytes, in the C type `N` that the kernel reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Len<N>(pub N);

/// A count of entries, of buffers, of files or of events, in the C type `N`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Count<N>(pub N);

/// An offset in a file or a pipe, in the C type `N` that the kernel reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Offset<N>(pub N);

/// An index in a table of the ring: a registered buffer, a slot of the file
/// table, a buffer group or a buffer of a group.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Index<N>(pub N);

/// A code that the kernel names: an operation, an advice, a direction of a
/// shutdown, a socket option's level or name, or the type of an id.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Code<N>(pub N);

/// The mode of a file that an entry makes or opens, in the C type `M`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Mode<M>(pub M);

/// The data that the kernel copies from an entry to its completion.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UserData(pub u64);

/// A string that ends in a zero byte and that the kernel reads: a path, a
/// link's target or an attribute's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Text(pub *const ::core::ffi::c_char);

/// The bytes that the kernel reads or writes, behind `P`: an attribute's
/// value, or the memory of the rings.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Bytes<P>(pub P);

/// An array of descriptors, behind `P`, that the kernel reads or fills.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fds<P>(pub P);

/// The word of a futex.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FutexWord(pub *const u32);

/// The value that the kernel compares with a futex's word.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Value(pub u64);

/// The id of a process or a group of processes, as its type reads it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Id(pub ::liburing_rs::id_t);

/// A setting that is on or off.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Switch(pub bool);

/// The answer of a predicate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Holds(pub bool);

/// The CPU that the thread of a polled submission queue runs on.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Cpu(pub u32);

/// A time in milliseconds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Millis(pub u32);

/// The answer of a liburing call or of a system call of the base, in the C
/// type `N`: zero or more is success, and a negative answer is its error
/// number. A decoder of the base gives it only for a success.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Answer<N>(pub N);
