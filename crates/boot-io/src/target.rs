//! The face of the crate on a target that it has no system call for.
//!
//! Each function here has the name and the signature of the function with the
//! system call, and one bound more: [`Host`] is [`Supported`]. No type is
//! [`Supported`]. So the crate compiles on the target, and each use of a
//! function is one error of the compiler, whose message names the target.
//!
//! The bound quantifies its own lifetime, so the compiler checks it at each
//! use and not at the definition, and the function has no generic parameter.
//! No function runs: each body reads [`Supported::NEVER`], a value of a type
//! with no value.

use core::convert::Infallible;
use core::marker::PhantomData;

use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_core::Range;

use crate::Descriptor;
use crate::Io;
use crate::Refused;

/// A target that the crate has the system calls of. No type implements it.
///
/// # Specification
/// trivial.
#[cfg_attr(
    all(target_os = "linux", target_arch = "riscv64"),
    diagnostic::on_unimplemented(
        message = "gandr-boot-io has no system call for the target riscv64gc-unknown-linux-gnu: it \
                   has the calls of x86_64-unknown-linux-gnu alone",
        label = "this function needs a system call of the target"
    )
)]
#[cfg_attr(
    all(target_os = "macos", target_arch = "aarch64"),
    diagnostic::on_unimplemented(
        message = "gandr-boot-io has no system call for the target aarch64-apple-darwin: it has \
                   the calls of x86_64-unknown-linux-gnu alone",
        label = "this function needs a system call of the target"
    )
)]
#[cfg_attr(
    not(any(
        all(target_os = "linux", target_arch = "riscv64"),
        all(target_os = "macos", target_arch = "aarch64"),
    )),
    diagnostic::on_unimplemented(
        message = "gandr-boot-io has no system call for this target: it has the calls of \
                   x86_64-unknown-linux-gnu alone",
        label = "this function needs a system call of the target"
    )
)]
pub trait Supported
{
    /// The value that a body reads: a function with this bound never runs.
    const NEVER: Infallible;
}

/// The target of the build, as the subject of the bound [`Supported`].
///
/// # Specification
/// trivial.
pub struct Host<'bound>(PhantomData<&'bound ()>);

/// [`start`](crate::start) on a target with no system call of the crate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// None: no use of the function compiles.
#[inline]
pub const fn start() -> Result<Io, Refused>
where
    for<'bound> Host<'bound>: Supported,
{
    match <Host<'_> as Supported>::NEVER {}
}

/// [`open`](crate::open) on a target with no system call of the crate.
///
/// # Safety
///
/// - unsafe invariants: none — no use of the function compiles.
///
/// # Specification
/// trivial.
///
/// # Errors
/// None: no use of the function compiles.
#[inline]
pub unsafe fn open(
    _io: &Io,
    _path: Range,
) -> Result<Descriptor, Refused>
where
    for<'bound> Host<'bound>: Supported,
{
    match <Host<'_> as Supported>::NEVER {}
}

/// [`read`](crate::read) on a target with no system call of the crate.
///
/// # Safety
///
/// - unsafe invariants: none — no use of the function compiles.
///
/// # Specification
/// trivial.
///
/// # Errors
/// None: no use of the function compiles.
#[inline]
pub unsafe fn read(
    _io: &Io,
    _descriptor: Descriptor,
    _place: Place,
) -> Result<Length, Refused>
where
    for<'bound> Host<'bound>: Supported,
{
    match <Host<'_> as Supported>::NEVER {}
}

/// [`write`](crate::write) on a target with no system call of the crate.
///
/// # Safety
///
/// - unsafe invariants: none — no use of the function compiles.
///
/// # Specification
/// trivial.
///
/// # Errors
/// None: no use of the function compiles.
#[inline]
pub unsafe fn write(
    _io: &Io,
    _descriptor: Descriptor,
    _bytes: Range,
) -> Result<Length, Refused>
where
    for<'bound> Host<'bound>: Supported,
{
    match <Host<'_> as Supported>::NEVER {}
}

/// [`close`](crate::close) on a target with no system call of the crate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// None: no use of the function compiles.
#[inline]
pub fn close(
    _io: &Io,
    _descriptor: Descriptor,
) -> Result<(), Refused>
where
    for<'bound> Host<'bound>: Supported,
{
    match <Host<'_> as Supported>::NEVER {}
}

/// [`stop`](crate::stop) on a target with no system call of the crate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// None: no use of the function compiles.
#[inline]
pub const fn stop(_io: Io) -> Result<(), Refused>
where
    for<'bound> Host<'bound>: Supported,
{
    match <Host<'_> as Supported>::NEVER {}
}
