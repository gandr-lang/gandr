//! The tests of the base's three calls on a ring of the host's kernel.

#[cfg(test)]
mod test
{
    use ::std::os::fd::AsFd as _;
    use ::std::os::fd::AsRawFd as _;

    use crate::arg::Answer;
    use crate::arg::Code;
    use crate::arg::Count;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::base::sys::linux::uapi::arch::io_uring_params;
    use crate::base::sys::linux::uapi::arch::io_uring_register_op_IORING_REGISTER_FILES;
    use crate::base::sys::linux::uapi::arch::io_uring_register_op_IORING_UNREGISTER_FILES;
    use crate::base::sys::linux::uapi::io_uring::io_uring_enter;
    use crate::base::sys::linux::uapi::io_uring::io_uring_register;
    use crate::base::sys::linux::uapi::io_uring::io_uring_register_with;
    use crate::base::sys::linux::uapi::io_uring::io_uring_setup;

    /// A ring of two entries sets up, and the call gives its descriptor.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it issues a system call by inline assembly, which Miri cannot run"
    )]
    fn setup() -> std::io::Result<()>
    {
        let entries = Count(2u32);
        let mut params = io_uring_params::default();
        let fd = { io_uring_setup(entries, &mut params) }?;
        drop(fd);
        Ok(())
    }

    /// A ring of no entries does not set up: the kernel answers `EINVAL`,
    /// and the base gives that error number.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it issues a system call by inline assembly, which Miri cannot run"
    )]
    fn setup_refuses_no_entries()
    {
        let mut params = io_uring_params::default();
        let refused = io_uring_setup(Count(0), &mut params);
        let errno = refused.expect_err("the kernel refuses a ring of no entries");
        assert_eq!(
            errno.into_raw_os_error(),
            Code(::libc::EINVAL),
            "the base gives the kernel's error number"
        );
    }

    /// A table of one open file registers on a ring through
    /// `io_uring_register`, and unregisters through `io_uring_register_with`.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it issues a system call by inline assembly, which Miri cannot run"
    )]
    fn register() -> ::std::io::Result<()>
    {
        let mut params = io_uring_params::default();
        let ring = io_uring_setup(Count(2), &mut params)?;
        let file = ::std::fs::File::open("/dev/null")?;
        let files = [file.as_raw_fd()];
        // SAFETY: `files` names one open descriptor, which the registration
        // reads alone.
        let registered = unsafe {
            io_uring_register(
                ring.as_fd(),
                Code(io_uring_register_op_IORING_REGISTER_FILES),
                (&raw const files).cast(),
                Count(1),
            )
        }?;
        assert_eq!(registered, Answer(0), "the kernel registers the table");
        // SAFETY: the unregistration reads no argument.
        let unregistered = unsafe {
            io_uring_register_with(
                ring.as_fd(),
                Code(io_uring_register_op_IORING_UNREGISTER_FILES),
                Flags(0),
                ::core::ptr::null(),
                Count(0),
            )
        }?;
        assert_eq!(unregistered, Answer(0), "the kernel unregisters the table");
        Ok(())
    }

    /// An enter that submits nothing and waits for nothing consumes no
    /// entry.
    #[test]
    #[cfg_attr(
        miri,
        ignore = "it issues a system call by inline assembly, which Miri cannot run"
    )]
    fn enter() -> ::std::io::Result<()>
    {
        let mut params = io_uring_params::default();
        let ring = io_uring_setup(Count(2), &mut params)?;
        // SAFETY: the call submits no entry and takes no extended argument.
        let consumed = unsafe {
            io_uring_enter(
                ring.as_fd(),
                Count(0),
                Count(0),
                Flags(0),
                ::core::ptr::null(),
                Len(0),
            )
        }?;
        assert_eq!(consumed, Answer(0), "the kernel consumes no entry");
        Ok(())
    }
}
