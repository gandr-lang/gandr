//! The answer of a liburing call as a result: a negative answer is an error
//! number.

// The crate's declarations of the kernel's `io_uring` header are the base's
// files under `base/sys/linux/uapi/arch`, one for each of six architectures,
// which the build script makes. #7692 owes the check of them against one
// pinned kernel.

use crate::arg::Answer;

/// The answer of a liburing call, read as a result.
pub trait SysResult: self::private::SysResult
{
    /// Zero as success, and any other answer as its error number.
    ///
    /// # Errors
    ///
    /// The answer is not zero.
    ///
    /// # Specification
    ///
    /// - fails: the answer is not zero.
    /// - executable: none — a trait declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero or a count is success, and a negative answer is
    ///   its error number.
    /// - declaration-only: the implementation for the kernel's answer carries
    ///   the witnesses.
    fn sys_zero(&self) -> ::std::io::Result<()>;
    /// A count as success, and a negative answer as its error number.
    ///
    /// # Errors
    ///
    /// The answer is negative.
    ///
    /// # Specification
    ///
    /// - fails: the answer is negative.
    /// - executable: none — a trait declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero or a count is success, and a negative answer is
    ///   its error number.
    /// - declaration-only: the implementation for the kernel's answer carries
    ///   the witnesses.
    fn sys_uint(&self) -> ::std::io::Result<Answer<::core::ffi::c_uint>>;
}

impl SysResult for Answer<::core::ffi::c_int>
{
    /// Zero as success, and any other answer as its error number.
    ///
    /// # Errors
    ///
    /// The answer is not zero.
    ///
    /// # Specification
    ///
    /// trivial.
    fn sys_zero(&self) -> ::std::io::Result<()>
    {
        if self.0 != 0i32 {
            return Err(::std::io::Error::from_raw_os_error(self.0.abs()));
        }
        Ok(())
    }

    /// A count as success, and a negative answer as its error number.
    ///
    /// # Errors
    ///
    /// The answer is negative.
    ///
    /// # Specification
    ///
    /// trivial.
    fn sys_uint(&self) -> ::std::io::Result<Answer<::core::ffi::c_uint>>
    {
        if self.0.is_negative() {
            return Err(::std::io::Error::from_raw_os_error(self.0.abs()));
        }
        #[expect(clippy::as_conversions, reason = "checked non-negative")]
        #[expect(clippy::cast_sign_loss, reason = "checked non-negative")]
        Ok(Answer(self.0 as ::core::ffi::c_uint))
    }
}

/// The seal: no type outside the crate reads an answer as a result.
mod private
{
    /// The sealed trait.
    pub trait SysResult
    {
    }
    impl self::SysResult for crate::arg::Answer<::core::ffi::c_int>
    {
    }
}

#[cfg(test)]
pub mod test
{
    use crate::arg::Answer;
    use crate::sys::SysResult as _;

    mod sys_result
    {
        use super::*;

        mod sys_zero
        {
            use super::*;

            #[test]
            fn ok()
            {
                let code = Answer(0i32);
                code.sys_zero().unwrap();
            }

            #[test]
            #[should_panic(
                expected = r#"called `Result::unwrap()` on an `Err` value: Os { code: 22, kind: InvalidInput, message: "Invalid argument"#
            )]
            fn err()
            {
                let code = Answer(-::rustix::io::Errno::INVAL.raw_os_error());
                code.sys_zero().unwrap();
            }
        }

        mod sys_uint
        {
            use super::*;

            #[test]
            fn ok()
            {
                let code = Answer(4096i32);
                assert_eq!(code.sys_uint().unwrap(), Answer(4096u32));
            }

            #[test]
            #[should_panic(
                expected = r#"called `Result::unwrap()` on an `Err` value: Os { code: 22, kind: InvalidInput, message: "Invalid argument"#
            )]
            fn err()
            {
                let code = Answer(-::rustix::io::Errno::INVAL.raw_os_error());
                code.sys_uint().unwrap();
            }
        }
    }
}
